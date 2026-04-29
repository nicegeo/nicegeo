import { Definition, Location, Position, Range } from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { runProofStateAt } from "./proofstate";

const DECL_RE = /\b(?:Theorem|Definition|Axiom)\s+([A-Za-z_][A-Za-z0-9_'.!?]*)/g;

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

function findSameFileDeclaration(doc: TextDocument, symbol: string): Location | null {
  const text = doc.getText();
  DECL_RE.lastIndex = 0;
  let match: RegExpExecArray | null;
  while ((match = DECL_RE.exec(text)) !== null) {
    if (match[1] !== symbol) continue;
    const nameOffset = match.index + match[0].lastIndexOf(symbol);
    const start = doc.positionAt(nameOffset);
    const end = doc.positionAt(nameOffset + symbol.length);
    return Location.create(doc.uri, Range.create(start, end));
  }
  return null;
}

export async function provideDefinition(
  doc: TextDocument,
  line: number,
  character: number,
  workspaceRoot?: string,
): Promise<Definition | null> {
  const symbol = getWordAtPosition(doc, line, character);
  if (!symbol) return null;

  const snapshot = await runProofStateAt(doc.uri, line, character, workspaceRoot);
  const decl = snapshot.declaration;
  if (snapshot.ok && decl && decl.name === symbol && decl.file) {
    const start: Position = {
      line: Math.max(0, decl.startLine - 1),
      character: Math.max(0, decl.startCol - 1),
    };
    const end: Position = {
      line: Math.max(0, decl.endLine - 1),
      character: Math.max(0, decl.endCol - 1),
    };
    return Location.create(decl.file, Range.create(start, end));
  }

  return findSameFileDeclaration(doc, symbol);
}

