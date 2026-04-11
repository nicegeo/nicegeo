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
  };
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

  return new Promise((resolve) => {
    const child = spawn(
      "dune",
      [
        "exec",
        "nicegeo-proofstate",
        "--",
        "--json",
        filePath,
        String(line1),
        String(col1),
      ],
      { cwd },
    );
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
    child.on("error", (err) => {
      resolve({
        ok: false,
        error: err instanceof Error ? err.message : String(err),
      });
    });
  });
}
