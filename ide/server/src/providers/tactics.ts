import { spawn } from "child_process";
import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from "url";

type ListTacticsResponse = {
  ok: boolean;
  tactics?: string[];
};

const CACHE_TTL_MS = 30_000;
let tacticCache: { ts: number; tactics: string[] } | null = null;
let inFlightRefresh: Promise<string[] | null> | null = null;

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

function parseJsonLineFromStdout(output: string): ListTacticsResponse | null {
  const lines = output.split(/\r?\n/);
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    const line = lines[i].trim();
    if (!line.startsWith("{")) continue;
    try {
      return JSON.parse(line) as ListTacticsResponse;
    } catch {
      continue;
    }
  }
  return null;
}

function runListTactics(cwd: string): Promise<string[] | null> {
  const args = ["exec", "nicegeo-proofstate", "--", "--list-tactics", "--json"];
  return new Promise((resolve) => {
    const child = spawn("dune", args, { cwd });
    const chunks: Buffer[] = [];
    const onData = (b: Buffer) => chunks.push(b);
    child.stdout.on("data", onData);
    child.stderr.on("data", onData);
    child.on("close", () => {
      const parsed = parseJsonLineFromStdout(Buffer.concat(chunks).toString("utf8"));
      if (parsed?.ok && Array.isArray(parsed.tactics)) {
        resolve(parsed.tactics);
        return;
      }
      resolve(null);
    });
    child.on("error", () => resolve(null));
  });
}

export async function getRegisteredTactics(documentUri: string, workspaceRoot?: string): Promise<string[]> {
  const filePath = fileURLToPath(documentUri);
  const repoRoot = findRepoRoot(filePath);
  const cwd = repoRoot ?? workspaceRoot ?? process.cwd();
  const now = Date.now();

  if (tacticCache && now - tacticCache.ts <= CACHE_TTL_MS) {
    return tacticCache.tactics;
  }

  if (tacticCache) {
    // Return stale cache immediately; refresh asynchronously to avoid blocking completion.
    if (!inFlightRefresh) {
      inFlightRefresh = runListTactics(cwd).then((tactics) => {
        if (tactics && tactics.length > 0) tacticCache = { ts: Date.now(), tactics };
        inFlightRefresh = null;
        return tactics;
      });
    }
    return tacticCache.tactics;
  }

  if (!inFlightRefresh) inFlightRefresh = runListTactics(cwd);
  const tactics = await inFlightRefresh;
  inFlightRefresh = null;
  if (tactics && tactics.length > 0) {
    tacticCache = { ts: Date.now(), tactics };
    return tactics;
  }
  return [];
}
