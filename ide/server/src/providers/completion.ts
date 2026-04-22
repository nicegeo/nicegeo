import {
  CompletionItem,
  CompletionItemKind,
  InsertTextFormat,
  MarkupKind,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { runProofStateAt } from "./proofstate";
import { getRegisteredTactics } from "./tactics";

type CompletionData = {
  source: "keyword" | "directive" | "operator" | "tactic" | "local" | "env" | "meta";
  type?: string;
  kindText?: string;
};

type CompletionContext = {
  expectDeclName: boolean;
  likelyDirective: boolean;
  onlyDirectives: boolean;
  inProof: boolean;
  atLineStart: boolean;
  inComment: boolean;
  shouldQuerySemantic: boolean;
};

const KEYWORDS = ["Theorem", "Definition", "Axiom", "Import", "Proof.", "Qed.", "fun", "Type", "Prop"];

const DIRECTIVES = [
  { label: "#infer", snippet: "#infer ${1:term}", detail: "Infer type of term" },
  { label: "#check", snippet: "#check ${1:term} : ${2:type}", detail: "Check term against type" },
  { label: "#reduce", snippet: "#reduce ${1:term}", detail: "Normalize term" },
  { label: "#opaque", snippet: "#opaque ${1:name}", detail: "Mark declaration as opaque" },
  { label: "#print axioms", snippet: "#print axioms ${1:name}", detail: "Print axioms used by declaration" },
];

const OPERATORS = ["->", "<->", "=>", ":=", "/\\", "\\/", "~", "=", "!="];
const TACTIC_SNIPPETS: Record<string, string> = {
  reflexivity: "reflexivity.",
  sorry: "sorry.",
  left: "left.",
  right: "right.",
  split: "split.",
  exact: "exact ${1:term}.",
  apply: "apply ${1:term}.",
  rewrite: "rewrite ${1:eqProof}.",
  exists: "exists ${1:witness}.",
  intro: "intro ${1:name}.",
  intros: "intros ${1:names}.",
  try: "try ${1:tactic}.",
  repeat: "repeat ${1:tactic}.",
  have: "have ${1:name} ${2:type}.",
  choose: "choose ${1:name1} ${2:name2} ${3:term}.",
};

const MAX_ITEMS = 120;
const CACHE_TTL_MS = 400;
const completionCache = new Map<string, { ts: number; items: CompletionItem[] }>();

function addUnique(items: CompletionItem[], item: CompletionItem, seen: Set<string>): void {
  const key = `${item.kind ?? 0}:${item.label}`;
  if (seen.has(key)) return;
  seen.add(key);
  items.push(item);
}

function isInsideProofBlock(doc: TextDocument, line0: number): boolean {
  const text = doc.getText();
  const lines = text.split(/\r?\n/);
  let inside = false;
  for (let i = 0; i <= Math.min(line0, lines.length - 1); i += 1) {
    const trimmed = lines[i].trim();
    if (trimmed === "Proof.") inside = true;
    if (trimmed === "Qed.") inside = false;
  }
  return inside;
}

function currentLinePrefix(doc: TextDocument, line0: number, col0: number): string {
  const line = doc.getText({
    start: { line: line0, character: 0 },
    end: { line: line0, character: col0 },
  });
  return line;
}

function collectDeclaredNames(doc: TextDocument, line0: number): string[] {
  const uptoLineText = doc.getText({
    start: { line: 0, character: 0 },
    end: { line: line0, character: 10_000 },
  });
  const re = /\b(?:Theorem|Definition|Axiom)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)/g;
  const out: string[] = [];
  let m: RegExpExecArray | null = re.exec(uptoLineText);
  while (m) {
    out.push(m[1]);
    m = re.exec(uptoLineText);
  }
  return out;
}

function classifyContext(prefix: string, inProof: boolean, atLineStart: boolean): CompletionContext {
  const inComment = /^\s*\(\*/.test(prefix);
  const likelyDirective = /^\s*#/.test(prefix);
  const onlyDirectives = likelyDirective;
  const expectDeclName =
    /^\s*(Theorem|Definition|Axiom)\s+[A-Za-z0-9_'.!?]*$/.test(prefix) ||
    /^\s*Import\s+[A-Za-z0-9_./-]*$/.test(prefix);

  const shouldQuerySemantic = !inComment && !onlyDirectives;

  return {
    expectDeclName,
    likelyDirective,
    onlyDirectives,
    inProof,
    atLineStart,
    inComment,
    shouldQuerySemantic,
  };
}

function mkData(data: CompletionData): CompletionData {
  return data;
}

export async function provideCompletionItems(
  doc: TextDocument,
  line0: number,
  col0: number,
  workspaceRoot?: string,
): Promise<CompletionItem[]> {
  const prefix = currentLinePrefix(doc, line0, col0);
  const inProof = isInsideProofBlock(doc, line0);
  const atLineStart = /^\s*$/.test(prefix) || /^\s*[A-Za-z_]*$/.test(prefix);
  const ctx = classifyContext(prefix, inProof, atLineStart);
  const cacheKey = [
    doc.uri,
    doc.version,
    line0,
    prefix,
    ctx.expectDeclName ? "decl" : "nodecl",
    ctx.onlyDirectives ? "dir" : "nodir",
    ctx.inProof ? "proof" : "noproof",
    ctx.atLineStart ? "line" : "inline",
  ].join("|");
  const now = Date.now();
  const cached = completionCache.get(cacheKey);
  if (cached && now - cached.ts <= CACHE_TTL_MS) return cached.items;

  const items: CompletionItem[] = [];
  const seen = new Set<string>();

  if (ctx.inComment) return [];

  // Right after declaration keywords, prioritize reusable declaration names only.
  if (ctx.expectDeclName) {
    for (const n of collectDeclaredNames(doc, line0)) {
      addUnique(
        items,
        {
          label: n,
          kind: CompletionItemKind.Reference,
          detail: "existing declaration name",
          sortText: "00",
          data: mkData({ source: "env" }),
        },
        seen,
      );
    }
  }

  // Level 1: syntax words/directives/operators.
  if (!ctx.onlyDirectives && !ctx.expectDeclName) {
    for (const kw of KEYWORDS) {
      addUnique(
        items,
        {
          label: kw,
          kind: CompletionItemKind.Keyword,
          detail: "NiceGeo keyword",
          sortText: "50",
          data: mkData({ source: "keyword" }),
        },
        seen,
      );
    }
  }
  for (const d of DIRECTIVES) {
    if (!ctx.likelyDirective && d.label.startsWith("#")) continue;
    addUnique(
      items,
      {
        label: d.label,
        kind: CompletionItemKind.Keyword,
        detail: d.detail,
        sortText: "30",
        insertText: d.snippet,
        insertTextFormat: InsertTextFormat.Snippet,
        data: mkData({ source: "directive" }),
      },
      seen,
    );
  }
  if (!ctx.onlyDirectives && !ctx.expectDeclName) {
    for (const op of OPERATORS) {
      addUnique(
        items,
        {
          label: op,
          kind: CompletionItemKind.Operator,
          detail: "NiceGeo operator",
          sortText: "60",
          data: mkData({ source: "operator" }),
        },
        seen,
      );
    }
  }

  // Level 4: tactic names (proof scripting).
  if (ctx.inProof && ctx.atLineStart && !ctx.onlyDirectives) {
    const tactics = await getRegisteredTactics(doc.uri, workspaceRoot);
    for (const tacticName of tactics) {
      const snippet = TACTIC_SNIPPETS[tacticName] ?? `${tacticName} \${1:arg}.`;
      addUnique(
        items,
        {
          label: tacticName,
          kind: CompletionItemKind.Function,
          detail: "Registered NiceGeo tactic",
          sortText: "00",
          insertText: snippet,
          insertTextFormat: InsertTextFormat.Snippet,
          data: mkData({ source: "tactic", kindText: "registered tactic" }),
        },
        seen,
      );
    }
  }

  // Levels 2 + 3: semantic context from proofstate snapshot.
  if (ctx.shouldQuerySemantic) {
    const snapshot = await runProofStateAt(doc.uri, line0, col0, workspaceRoot);
    if (!(snapshot.ok && snapshot.proofState)) return items.slice(0, MAX_ITEMS);
    const ps = snapshot.proofState;

    for (const h of ps.hyps) {
      addUnique(
        items,
        {
          label: h.name,
          kind: CompletionItemKind.Variable,
          detail: h.type,
          sortText: "20",
          data: mkData({ source: "local", type: h.type }),
        },
        seen,
      );
    }
    for (const c of ps.termContext) {
      addUnique(
        items,
        {
          label: c.name,
          kind: CompletionItemKind.Variable,
          detail: c.type,
          sortText: "21",
          data: mkData({ source: "local", type: c.type }),
        },
        seen,
      );
    }
    for (const c of ps.headContext) {
      addUnique(
        items,
        {
          label: c.name,
          kind: CompletionItemKind.Variable,
          detail: c.type,
          sortText: "22",
          data: mkData({ source: "local", type: c.type }),
        },
        seen,
      );
    }
    for (const e of ps.environment ?? []) {
      const itemKind =
        e.kind === "axiom"
          ? CompletionItemKind.Constant
          : e.kind === "definition"
            ? CompletionItemKind.Variable
            : CompletionItemKind.Function;
      addUnique(
        items,
        {
          label: e.name,
          kind: itemKind,
          detail: `${e.kind}: ${e.type}`,
          sortText: ctx.expectDeclName ? "10" : "40",
          data: mkData({ source: "env", kindText: e.kind, type: e.type }),
        },
        seen,
      );
    }
    for (const m of ps.metas ?? []) {
      const label = `?m${m.id}`;
      const typeText = m.type ?? "(unknown type)";
      addUnique(
        items,
        {
          label,
          kind: CompletionItemKind.Reference,
          detail: `meta: ${typeText}`,
          sortText: "45",
          data: mkData({ source: "meta", type: typeText }),
        },
        seen,
      );
    }
  }

  const finalItems = items.slice(0, MAX_ITEMS);
  completionCache.set(cacheKey, { ts: now, items: finalItems });
  if (completionCache.size > 300) {
    // Keep cache bounded to avoid growth in long sessions.
    let n = 0;
    for (const k of completionCache.keys()) {
      completionCache.delete(k);
      n += 1;
      if (n >= 100) break;
    }
  }
  return finalItems;
}

export function resolveCompletionItem(item: CompletionItem): CompletionItem {
  const data = item.data as CompletionData | undefined;
  if (!data) return item;
  const details: string[] = [];
  details.push(`Source: ${data.source}`);
  if (data.kindText) details.push(`Kind: ${data.kindText}`);
  if (data.type) details.push(`Type: ${data.type}`);
  item.documentation = {
    kind: MarkupKind.Markdown,
    value: details.map((x) => `- ${x}`).join("\n"),
  };
  return item;
}

