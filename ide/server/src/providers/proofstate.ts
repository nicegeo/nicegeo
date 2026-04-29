import * as fs from "fs";
import * as path from "path";
import { spawn } from "child_process";
import { fileURLToPath } from "url";

/** Response shape from `nicegeo-proofstate --json` (stdout JSON line). */
export interface ProofStateAtResponse {
  ok: boolean;
  query?: { file: string; line: number; col: number };
  error?: string;
  declaration?: {
    name: string;
    kind: string;
    file: string;
    startLine: number;
    startCol: number;
    endLine: number;
    endCol: number;
  };
  proofState?: {
    goalType: string;
    goalTypeReduced?: string;
    headContext: { name: string; type: string }[];
    termContext: { name: string; type: string }[];
    hyps: { name: string; bid: number; type: string }[];
    environment?: { name: string; kind: string; type: string }[];
    metas?: { id: number; type: string | null; solution: string | null; context: number[] }[];
    tacticSteps?: {
      index: number;
      name: string;
      args: string[];
      documentation?: TacticDocumentation | null;
      goalBefore: string | null;
      goalsAfter: string[];
      status: string;
      atCursor: boolean;
    }[];
    tacticsApplied?: number;
    /** Pretty-printed open goals (same order as the prover stack; goal 1 is focused). */
    openGoals?: string[];
  };
}

export interface TacticDocumentation {
  oneLiner: string;
  expectedParameters: string;
  exampleUsage: string;
}

export interface TacticSpec {
  name: string;
  documentation: TacticDocumentation;
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

function toolMissingMessage(tool: string, cwd: string): string {
  if (tool === "dune") {
    return [
      "Could not start `dune` (not found in PATH).",
      "Install OCaml tooling and dune, then reopen VS Code from a shell where opam is active.",
      `Working directory: ${cwd}`,
    ].join("\n");
  }
  if (tool === "opam") {
    return [
      "Could not start `opam` (not found in PATH).",
      "Install opam, then run `opam install . --deps-only` in the project.",
      `Working directory: ${cwd}`,
    ].join("\n");
  }
  return `Could not start '${tool}' (not found in PATH).`;
}

/** `dune exec` may print "Entering directory" lines before the JSON line. */
function parseJsonLineFromStdout(output: string): ProofStateAtResponse | null {
  const lines = output.split(/\r?\n/);
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    const line = lines[i].trim();
    if (!line.startsWith("{")) continue;
    try {
      return JSON.parse(line) as ProofStateAtResponse;
    } catch {
      continue;
    }
  }
  return null;
}

function parseJsonObjectLine<T>(output: string): T | null {
  const lines = output.split(/\r?\n/);
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    const line = lines[i].trim();
    if (!line.startsWith("{")) continue;
    try {
      return JSON.parse(line) as T;
    } catch {
      continue;
    }
  }
  return null;
}

/**
 * Runs `nicegeo-proofstate --json` at a 1-based line/col (matching the CLI).
 * [line0], [col0] are VS Code 0-based position values.
 */
export function runProofStateAt(
  documentUri: string,
  line0: number,
  col0: number,
  workspaceRoot?: string,
): Promise<ProofStateAtResponse> {
  const filePath = fileURLToPath(documentUri);
  const line1 = line0 + 1;
  const col1 = col0 + 1;
  const repoRoot = findRepoRoot(filePath);
  const cwd = repoRoot ?? workspaceRoot ?? process.cwd();

  const duneExecByPathArgs = [
    "exec",
    ...(repoRoot ? ["--root", repoRoot] : []),
    "./bin/proofstate.exe",
    "--",
    "--json",
    filePath,
    String(line1),
    String(col1),
  ];
  const duneExecByPublicNameArgs = [
    "exec",
    ...(repoRoot ? ["--root", repoRoot] : []),
    "nicegeo-proofstate",
    "--",
    "--json",
    filePath,
    String(line1),
    String(col1),
  ];
  const attempts: Array<{ cmd: string; args: string[] }> = [
    { cmd: "dune", args: duneExecByPathArgs },
    { cmd: "dune", args: duneExecByPublicNameArgs },
    { cmd: "opam", args: ["exec", "--", "dune", ...duneExecByPathArgs] },
    { cmd: "opam", args: ["exec", "--", "dune", ...duneExecByPublicNameArgs] },
  ];

  const runAttempt = (idx: number): Promise<ProofStateAtResponse> =>
    new Promise((resolve) => {
      const attempt = attempts[idx];
      const child = spawn(attempt.cmd, attempt.args, { cwd });
      const chunks: Buffer[] = [];
      const onData = (b: Buffer) => chunks.push(b);
      child.stdout.on("data", onData);
      child.stderr.on("data", onData);
      child.on("close", (exitCode) => {
        const output = Buffer.concat(chunks).toString("utf8");
        const parsed = parseJsonLineFromStdout(output);
        if (parsed) {
          resolve(parsed);
          return;
        }
        resolve({
          ok: false,
          error:
            exitCode !== 0
              ? output.trim() || `nicegeo exited with code ${exitCode}`
              : "Could not parse proof state JSON from nicegeo output.",
        });
      });
      child.on("error", (err: NodeJS.ErrnoException) => {
        if (err?.code === "ENOENT" && idx + 1 < attempts.length) {
          void runAttempt(idx + 1).then(resolve);
          return;
        }
        if (err?.code === "ENOENT") {
          resolve({ ok: false, error: toolMissingMessage(attempt.cmd, cwd) });
          return;
        }
        resolve({ ok: false, error: err instanceof Error ? err.message : String(err) });
      });
    });

  return runAttempt(0);
}

const tacticSpecsCacheByRoot = new Map<string, TacticSpec[]>();
const tacticSpecsInFlightByRoot = new Map<string, Promise<TacticSpec[]>>();

function resolveRepoRoot(documentUri?: string, workspaceRoot?: string): string {
  if (documentUri) {
    try {
      const filePath = fileURLToPath(documentUri);
      const root = findRepoRoot(filePath);
      if (root) return root;
    } catch {
      // ignore and continue fallback
    }
  }
  return workspaceRoot ?? process.cwd();
}

export function getCachedTacticSpec(name: string, documentUri?: string, workspaceRoot?: string): TacticSpec | null {
  const repoRoot = resolveRepoRoot(documentUri, workspaceRoot);
  const cached = tacticSpecsCacheByRoot.get(repoRoot);
  if (!cached) return null;
  return cached.find((t) => t.name === name) ?? null;
}

export function getTacticSpecs(documentUri?: string, workspaceRoot?: string): Promise<TacticSpec[]> {
  const repoRoot = resolveRepoRoot(documentUri, workspaceRoot);
  const cached = tacticSpecsCacheByRoot.get(repoRoot);
  if (cached) return Promise.resolve(cached);
  const inFlight = tacticSpecsInFlightByRoot.get(repoRoot);
  if (inFlight) return inFlight;
  const args = ["exec", "--root", repoRoot, "./bin/proofstate.exe", "--", "--tactic-specs-json"];
  const attempts: Array<{ cmd: string; args: string[] }> = [
    { cmd: "dune", args },
    { cmd: "opam", args: ["exec", "--", "dune", ...args] },
  ];

  const runAttempt = (idx: number): Promise<TacticSpec[]> =>
    new Promise((resolve) => {
      const attempt = attempts[idx];
      const child = spawn(attempt.cmd, attempt.args, { cwd: repoRoot });
      const chunks: Buffer[] = [];
      const onData = (b: Buffer) => chunks.push(b);
      child.stdout.on("data", onData);
      child.stderr.on("data", onData);
      child.on("close", () => {
        const output = Buffer.concat(chunks).toString("utf8");
        const parsed = parseJsonObjectLine<{ ok?: boolean; tactics?: TacticSpec[] }>(output);
        if (parsed?.ok && Array.isArray(parsed.tactics)) {
          tacticSpecsCacheByRoot.set(repoRoot, parsed.tactics);
          resolve(parsed.tactics);
          return;
        }
        resolve([]);
      });
      child.on("error", (err: NodeJS.ErrnoException) => {
        if (err?.code === "ENOENT" && idx + 1 < attempts.length) {
          void runAttempt(idx + 1).then(resolve);
          return;
        }
        resolve([]);
      });
    });

  const promise = runAttempt(0).finally(() => {
    tacticSpecsInFlightByRoot.delete(repoRoot);
  });
  tacticSpecsInFlightByRoot.set(repoRoot, promise);
  return promise;
}
