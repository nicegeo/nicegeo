import * as fs from "fs";
import * as path from "path";
import { spawn } from "child_process";
import { fileURLToPath } from "url";
import {
  Diagnostic,
  DiagnosticSeverity,
  Range,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";

export type DiagnosticsTriggerMode = "onSave" | "onType" | "both";

export interface NiceGeoSettings {
  trigger: DiagnosticsTriggerMode;
  debounceMs: number;
}

export interface StatusReporter {
  checking: (uri: string, detail: string) => void;
  ok: (uri: string) => void;
  issues: (uri: string, count: number) => void;
}

type ParsedLoc =
  | { kind: "single"; file: string; line: number; colStart: number; colEnd: number }
  | { kind: "multi"; file: string; line1: number; col1: number; line2: number; col2: number };

const singleLineLocRe =
  /(?<file>(?:\/|\.\/|\.\.\/)?[A-Za-z0-9._/\-]+\.ncg):(?<line>\d+):(?<colStart>\d+)-(?<colEnd>\d+)\b/;
const multiLineLocRe =
  /(?<file>(?:\/|\.\/|\.\.\/)?[A-Za-z0-9._/\-]+\.ncg):(?<line1>\d+):(?<col1>\d+)\s+to\s+(?<line2>\d+):(?<col2>\d+)\b/;

function parseLocFromLine(line: string): ParsedLoc | null {
  const m2 = line.match(multiLineLocRe);
  if (m2?.groups) {
    return {
      kind: "multi",
      file: m2.groups.file,
      line1: Number(m2.groups.line1),
      col1: Number(m2.groups.col1),
      line2: Number(m2.groups.line2),
      col2: Number(m2.groups.col2),
    };
  }

  const m1 = line.match(singleLineLocRe);
  if (m1?.groups) {
    return {
      kind: "single",
      file: m1.groups.file,
      line: Number(m1.groups.line),
      colStart: Number(m1.groups.colStart),
      colEnd: Number(m1.groups.colEnd),
    };
  }
  return null;
}

function findRepoRoot(startFilePath: string): string | null {
  let dir = path.dirname(startFilePath);
  while (true) {
    const candidate = path.join(dir, "dune-project");
    if (fs.existsSync(candidate)) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}

function normalizeFsPath(p: string): string {
  return path.normalize(p);
}

function resolveLocPath(locFile: string, cwd: string): string {
  if (path.isAbsolute(locFile)) return locFile;
  return path.resolve(cwd, locFile);
}

function lineLength(doc: TextDocument, zeroBasedLine: number): number {
  const text = doc.getText();
  const lines = text.split(/\r?\n/);
  if (zeroBasedLine < 0 || zeroBasedLine >= lines.length) return 0;
  return lines[zeroBasedLine].length;
}

function toRange(loc: ParsedLoc, doc: TextDocument): Range {
  const maxLine = Math.max(0, doc.lineCount - 1);
  const clampLine = (n: number) => Math.max(0, Math.min(maxLine, n));
  const clampCol = (line: number, col: number) => {
    const maxCol = lineLength(doc, clampLine(line));
    return Math.max(0, Math.min(maxCol, col));
  };

  if (loc.kind === "single") {
    const line0 = clampLine(loc.line - 1);
    const startChar = clampCol(line0, loc.colStart - 1);
    let endChar = clampCol(line0, loc.colEnd - 1);
    if (endChar <= startChar) endChar = Math.min(startChar + 1, lineLength(doc, line0));
    return Range.create(line0, startChar, line0, endChar);
  }

  const lineStart0 = clampLine(loc.line1 - 1);
  const lineEnd0 = clampLine(loc.line2 - 1);
  const startChar = clampCol(lineStart0, loc.col1 - 1);
  const endChar = clampCol(lineEnd0, loc.col2 - 1);
  return Range.create(lineStart0, startChar, lineEnd0, endChar);
}

function parseDiagnostics(output: string, doc: TextDocument, cwd: string): Diagnostic[] {
  const docPath = normalizeFsPath(fileURLToPath(doc.uri));
  const diagnostics: Diagnostic[] = [];
  const lines = output.split(/\r?\n/);

  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    const loc = parseLocFromLine(line.trim());
    if (!loc) continue;

    const locPath = normalizeFsPath(resolveLocPath(loc.file, cwd));
    if (locPath !== docPath) continue;

    let message = line.trim();
    const next = lines[i + 1]?.trim() ?? "";
    if (next.startsWith("Did you mean:")) {
      message = `${message}\n${next}`;
    }

    diagnostics.push({
      range: toRange(loc, doc),
      severity: DiagnosticSeverity.Error,
      source: "nicegeo",
      message: message || "NiceGeo error",
    });
  }

  if (diagnostics.length === 0 && output.trim().length > 0) {
    diagnostics.push({
      range: Range.create(0, 0, 0, 1),
      severity: DiagnosticSeverity.Error,
      source: "nicegeo",
      message: output.trim(),
    });
  }

  return diagnostics;
}

export class DiagnosticsService {
  private readonly running = new Map<string, { seq: number; child?: ReturnType<typeof spawn> }>();
  private readonly timers = new Map<string, NodeJS.Timeout>();

  constructor(
    private readonly status: StatusReporter,
    private readonly publish: (uri: string, diagnostics: Diagnostic[]) => void,
  ) {}

  dispose() {
    for (const t of this.timers.values()) clearTimeout(t);
    this.timers.clear();
    for (const v of this.running.values()) v.child?.kill();
    this.running.clear();
  }

  clear(uri: string) {
    this.publish(uri, []);
  }

  request(doc: TextDocument, reason: "save" | "type", settings: NiceGeoSettings, workspaceRoot?: string) {
    const allowed =
      reason === "save"
        ? settings.trigger === "onSave" || settings.trigger === "both"
        : settings.trigger === "onType" || settings.trigger === "both";
    if (!allowed) return;

    const key = doc.uri;
    const debounce = reason === "type" ? settings.debounceMs : 0;
    const existing = this.timers.get(key);
    if (existing) clearTimeout(existing);

    if (debounce > 0) {
      this.timers.set(
        key,
        setTimeout(() => {
          this.timers.delete(key);
          void this.runNow(doc, workspaceRoot);
        }, debounce),
      );
    } else {
      void this.runNow(doc, workspaceRoot);
    }
  }

  async runNow(doc: TextDocument, workspaceRoot?: string) {
    const key = doc.uri;
    const prev = this.running.get(key);
    const seq = (prev?.seq ?? 0) + 1;
    prev?.child?.kill();
    this.running.set(key, { seq });

    const filePath = fileURLToPath(doc.uri);
    const repoRoot = findRepoRoot(filePath);
    const cwd = repoRoot ?? workspaceRoot ?? process.cwd();

    this.status.checking(doc.uri, `dune exec nicegeo -- ${filePath}`);

    const result = await new Promise<{ seq: number; exitCode: number | null; output: string }>((resolve) => {
      const child = spawn("dune", ["exec", "nicegeo", "--", filePath], { cwd });
      const chunks: Buffer[] = [];
      const onData = (b: Buffer) => chunks.push(b);
      child.stdout.on("data", onData);
      child.stderr.on("data", onData);

      const current = this.running.get(key);
      if (current) current.child = child;

      child.on("close", (exitCode) => {
        resolve({ seq, exitCode, output: Buffer.concat(chunks).toString("utf8") });
      });
      child.on("error", (err) => {
        resolve({ seq, exitCode: 1, output: String(err?.message ?? err) });
      });
    });

    const latest = this.running.get(key);
    if (!latest || latest.seq !== result.seq) return;

    if (result.exitCode === 0) {
      this.publish(doc.uri, []);
      this.status.ok(doc.uri);
      return;
    }

    const diagnostics = parseDiagnostics(result.output, doc, cwd);
    this.publish(doc.uri, diagnostics);
    this.status.issues(doc.uri, diagnostics.length);
  }
}

