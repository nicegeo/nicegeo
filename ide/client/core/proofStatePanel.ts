import * as vscode from "vscode";

export interface ProofStateAtPayload {
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
    /** β-reduced goal type (may equal goalType). */
    goalTypeReduced?: string;
    headContext: { name: string; type: string }[];
    headContextReduced?: { name: string; type: string }[];
    termContext: { name: string; type: string }[];
    hyps: { name: string; bid: number; type: string }[];
    /** Global names in scope before this declaration (axiom / theorem / definition). */
    environment?: { name: string; kind: string; type: string }[];
    /** Metavariables (holes) in the elaboration context. */
    metas?: { id: number; type: string | null; solution: string | null; context: number[] }[];
  };
}

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function section(title: string, body: string): string {
  return `<section class="block"><h2>${escapeHtml(title)}</h2>${body}</section>`;
}

function listItems(rows: { label: string; value: string }[]): string {
  if (rows.length === 0) return `<p class="muted">(none)</p>`;
  return `<ul>${rows.map((r) => `<li><span class="name">${escapeHtml(r.label)}</span> : ${escapeHtml(r.value)}</li>`).join("")}</ul>`;
}

function buildHtml(data: ProofStateAtPayload): string {
  if (!data.ok) {
    const err = data.error ?? "Unknown error";
    const q = data.query;
    const posHint =
      q && !err.includes(String(q.line))
        ? ` (line ${q.line}, column ${q.col})`
        : "";
    return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
      body { font-family: var(--vscode-font-family); font-size: 13px; color: var(--vscode-foreground); padding: 12px; }
      .err { color: var(--vscode-errorForeground); white-space: pre-wrap; }
      .muted { opacity: 0.75; }
    </style></head><body>
      <p class="err">${escapeHtml(err)}${escapeHtml(posHint)}</p>
    </body></html>`;
  }

  const decl = data.declaration;
  const ps = data.proofState;
  const declBlock =
    decl &&
    section(
      "Declaration",
      `<p><strong>${escapeHtml(decl.name)}</strong> <span class="muted">(${escapeHtml(decl.kind)})</span></p>`,
    );

  if (!ps) {
    return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
      body { font-family: var(--vscode-font-family); padding: 12px; }
    </style></head><body>${declBlock ?? ""}<p>No proof state.</p></body></html>`;
  }

  const reduced =
    ps.goalTypeReduced !== undefined && ps.goalTypeReduced !== ps.goalType
      ? section(
          "Goal (β-reduced)",
          `<p class="goal">⊢ ${escapeHtml(ps.goalTypeReduced)}</p>`,
        )
      : "";

  const goal = section("Goal", `<p class="goal">⊢ ${escapeHtml(ps.goalType)}</p>`);
  const head = section(
    "Head context (intro binders)",
    listItems(ps.headContext.map((c) => ({ label: c.name, value: c.type }))),
  );
  const headRed =
    ps.headContextReduced && ps.headContextReduced.length > 0
      ? section(
          "Head context (from reduced goal)",
          listItems(ps.headContextReduced.map((c) => ({ label: c.name, value: c.type }))),
        )
      : "";

  const term = section(
    "Term context (at cursor)",
    listItems(ps.termContext.map((c) => ({ label: c.name, value: c.type }))),
  );

  const envList = ps.environment ?? [];
  const envBlock =
    envList.length === 0
      ? ""
      : `<details class="fold"><summary>Global environment (${envList.length} names)</summary>${listItems(
          envList.map((e) => ({ label: `${e.name} (${e.kind})`, value: e.type })),
        )}</details>`;

  const metaList = ps.metas ?? [];
  const metaBlock =
    metaList.length === 0
      ? ""
      : `<details class="fold"><summary>Metas (${metaList.length})</summary><ul>${metaList
          .map((m) => {
            const ty = m.type != null ? ` : ${escapeHtml(m.type)}` : "";
            const sol = m.solution != null ? ` := ${escapeHtml(m.solution)}` : "";
            const ctx =
              m.context && m.context.length > 0
                ? ` <span class="muted">ctx=[${m.context.join(",")}]</span>`
                : "";
            return `<li class="mono">?${m.id}${ty}${sol}${ctx}</li>`;
          })
          .join("")}</ul></details>`;

  const hyps = section(
    "Goal hypotheses",
    listItems(
      ps.hyps.map((h) => ({
        label: `${h.name} [${h.bid}]`,
        value: h.type,
      })),
    ),
  );

  return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
    body { font-family: var(--vscode-font-family); font-size: 13px; color: var(--vscode-foreground); padding: 12px; }
    h2 { font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; margin: 16px 0 8px; color: var(--vscode-descriptionForeground); }
    .block:first-child h2 { margin-top: 0; }
    .goal { font-family: var(--vscode-editor-font-family); font-size: 13px; }
    .name { font-weight: 600; }
    ul { padding-left: 18px; margin: 8px 0; }
    li { margin: 4px 0; font-family: var(--vscode-editor-font-family); font-size: 12px; }
    .muted { opacity: 0.8; }
    details.fold { margin: 12px 0; }
    details.fold summary { cursor: pointer; font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--vscode-descriptionForeground); margin-bottom: 8px; }
    li.mono { font-family: var(--vscode-editor-font-family); font-size: 12px; margin: 4px 0; }
  </style></head><body>
    ${declBlock ?? ""}
    ${goal}
    ${reduced}
    ${head}
    ${headRed}
    ${term}
    ${envBlock}
    ${metaBlock}
    ${hyps}
  </body></html>`;
}

let panel: vscode.WebviewPanel | undefined;

export function showProofStatePanel(data: ProofStateAtPayload): void {
  const column = vscode.ViewColumn.Beside;
  const title =
    data.ok && data.declaration?.name
      ? `Proof: ${data.declaration.name}`
      : "NiceGeo proof state";
  if (panel) {
    panel.title = title;
    panel.webview.html = buildHtml(data);
    panel.reveal(column, true);
  } else {
    panel = vscode.window.createWebviewPanel(
      "nicegeoProofState",
      title,
      column,
      { enableScripts: false, retainContextWhenHidden: true },
    );
    panel.webview.html = buildHtml(data);
    panel.onDidDispose(() => {
      panel = undefined;
    });
  }
}
