import { Hover, MarkupKind } from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { ProofStateAtResponse, getCachedTacticSpec, getTacticSpecs, runProofStateAt } from "./proofstate";

const KEYWORD_DOCS: Record<string, string> = {
  Theorem: "Introduces a theorem declaration.",
  Axiom: "Introduces an axiom declaration.",
  Definition: "Introduces a definition declaration.",
  fun: "Lambda/function literal.",
};

function getWordAtPosition(doc: TextDocument, line: number, character: number): string | null {
  const lineStart = doc.offsetAt({ line, character: 0 });
  const lineEnd = doc.offsetAt({ line, character: Number.MAX_SAFE_INTEGER });
  const text = doc.getText();
  const lineText = text.slice(lineStart, lineEnd);
  const idx = Math.max(0, Math.min(character, lineText.length));
  const isWord = (c: string) => /[A-Za-z0-9_'.!?]/.test(c);

  let l = idx;
  while (l > 0 && isWord(lineText[l - 1])) l -= 1;
  let r = idx;
  while (r < lineText.length && isWord(lineText[r])) r += 1;
  if (l === r) return null;
  return lineText.slice(l, r);
}

function normalizeHoverSymbol(raw: string): string {
  return raw.replace(/[.,;:]+$/g, "");
}

function formatSymbolCard(kind: string, name: string, type: string, file?: string): string {
  const parts = [
    `### ${kind} ${name}`,
    "```nicegeo",
    `${name} : ${type}`,
    "```",
  ];
  if (file) parts.push(`Defined in \`${file}\``);
  return parts.join("\n");
}

function formatTacticDoc(name: string, oneLiner: string, expected: string, example: string): string {
  const parts = [`### tactic ${name}`];
  if (oneLiner.trim()) parts.push(oneLiner);
  parts.push("**Expected parameters**");
  parts.push("```nicegeo");
  parts.push(`${name} ${expected}`.trim());
  parts.push("```");
  if (example.trim()) {
    parts.push("**Example usage**");
    parts.push("```nicegeo");
    parts.push(example);
    parts.push("```");
  }
  return parts.join("\n");
}

function formatHoverMarkdown(symbol: string | null, snapshot: ProofStateAtResponse): string | null {
  if (!symbol) return null;
  if (!snapshot.ok || !snapshot.proofState) {
    if (snapshot.error) {
      return [`### NiceGeo`, "```text", snapshot.error, "```"].join("\n");
    }
    return null;
  }
  const ps = snapshot.proofState;
  const parts: string[] = [];
  const hyps = ps.hyps ?? [];
  const termContext = ps.termContext ?? [];
  const environment = ps.environment ?? [];
  const tacticAtCursor = (ps.tacticSteps ?? []).find((s) => s.atCursor);
  if (tacticAtCursor && symbol === tacticAtCursor.name) {
    const doc = tacticAtCursor.documentation;
    return formatTacticDoc(
      tacticAtCursor.name,
      doc?.oneLiner ?? "",
      doc?.expectedParameters ?? "",
      doc?.exampleUsage ?? "",
    );
  }

  const local = hyps.find((h) => h.name === symbol);
  if (local) {
    parts.push(formatSymbolCard("local", local.name, local.type));
  } else {
    const term = termContext.find((t) => t.name === symbol);
    if (term) {
      parts.push(formatSymbolCard("local", term.name, term.type));
    }
    const env = environment.find((e) => e.name === symbol);
    if (env) {
      parts.push(formatSymbolCard(env.kind, env.name, env.type));
    }
    if (!env && snapshot.declaration?.name === symbol) {
      const d = snapshot.declaration;
      const envLike = environment.find((e) => e.name === d.name);
      if (envLike) {
        parts.push(formatSymbolCard(envLike.kind, envLike.name, envLike.type, d.file));
      } else {
        parts.push(`### ${d.kind} ${d.name}`);
        if (d.file) parts.push(`Defined in \`${d.file}\``);
      }
    }
  }

  if (parts.length === 0) return null;
  return parts.join("\n");
}

export async function provideHover(
  doc: TextDocument,
  line: number,
  character: number,
  workspaceRoot?: string,
): Promise<Hover | null> {
  const rawSymbol = getWordAtPosition(doc, line, character);
  if (!rawSymbol) return null;
  const symbol = normalizeHoverSymbol(rawSymbol);
  if (!symbol) return null;
  if (KEYWORD_DOCS[symbol]) {
    return {
      contents: {
        kind: MarkupKind.Markdown,
        value: `### keyword \`${symbol}\`\n${KEYWORD_DOCS[symbol]}`,
      },
    };
  }
  // Fastest path: synchronous cache lookup first (avoids loading flicker on repeat hover).
  let spec = getCachedTacticSpec(symbol, doc.uri, workspaceRoot);
  if (!spec) {
    const tacticSpecs = await getTacticSpecs(doc.uri, workspaceRoot);
    spec = tacticSpecs.find((t) => t.name === symbol) ?? null;
  }
  if (spec) {
    const doc = spec.documentation;
    return {
      contents: {
        kind: MarkupKind.Markdown,
        value: formatTacticDoc(spec.name, doc.oneLiner, doc.expectedParameters, doc.exampleUsage),
      },
    };
  }
  const snapshot = await runProofStateAt(doc.uri, line, character, workspaceRoot);
  const markdown = formatHoverMarkdown(symbol, snapshot);
  if (!markdown) return null;
  return {
    contents: {
      kind: MarkupKind.Markdown,
      value: markdown,
    },
  };
}

