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
    termContext: { name: string; type: string }[];
    hyps: { name: string; bid: number; type: string }[];
    /** Global names in scope before this declaration (axiom / theorem / definition). */
    environment?: { name: string; kind: string; type: string }[];
    /** Metavariables (holes) in the elaboration context. */
    metas?: { id: number; type: string | null; solution: string | null; context: number[] }[];
    /** Step-by-step tactic execution info for theorem proof scripts. */
    tacticSteps?: {
      index: number;
      name: string;
      args: string[];
      goalBefore: string | null;
      goalsAfter: string[];
      status: string;
      atCursor: boolean;
    }[];
    tacticsApplied?: number;
    /** All open goals, same order as kernel; index 0 is the focused goal. */
    openGoals?: string[];
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


function renderFriendlyTerm(raw: string, hyps: { name: string; bid: number; type: string }[]): string {
  const byBid = new Map<number, string>();
  for (const h of hyps) {
    byBid.set(h.bid, h.name);
  }
  return raw.replace(/!(\d+)/g, (_m, g1) => {
    const bid = Number(g1);
    const name = byBid.get(bid);
    return name ?? `!${g1}`;
  });
}

function friendlyCtxNames(ctxBids: number[], hyps: { name: string; bid: number; type: string }[]): string[] {
  const byBid = new Map<number, string>();
  for (const h of hyps) {
    byBid.set(h.bid, h.name);
  }
  return ctxBids.map((bid) => byBid.get(bid) ?? `#${bid}`);
}

function compactMetaLabel(metaId: number): string {
  return `m${metaId}`;
}

export function buildProofStateHtml(data: ProofStateAtPayload): string {
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
  const tacticScriptHint =
    (ps?.tacticSteps?.length ?? 0) > 0
      ? `<p class="muted" style="font-size:12px;margin-top:8px">Executed tactics are highlighted; remaining tactics are dimmed.</p>`
      : "";
  const declBlock =
    decl &&
    section(
      "Declaration",
      `<p><strong>${escapeHtml(decl.name)}</strong> <span class="muted">(${escapeHtml(decl.kind)})</span></p>${tacticScriptHint}`,
    );

  if (!ps) {
    return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
      body { font-family: var(--vscode-font-family); padding: 12px; }
    </style></head><body>${declBlock ?? ""}<p>No proof state.</p></body></html>`;
  }

  const goalFriendly = renderFriendlyTerm(ps.goalType, ps.hyps);
  const reducedFriendly =
    ps.goalTypeReduced !== undefined ? renderFriendlyTerm(ps.goalTypeReduced, ps.hyps) : undefined;

  const reduced =
    reducedFriendly !== undefined && reducedFriendly !== goalFriendly
      ? section(
          "Goal (β-reduced)",
          `<p class="goal">⊢ ${escapeHtml(reducedFriendly)}</p>`,
        )
      : "";

  const openGoals = ps.openGoals ?? [];
  const otherOpenGoals = openGoals.length > 1 ? openGoals.slice(1) : [];
  const otherGoalsBlock =
    otherOpenGoals.length > 0
      ? section(
          `Other open goals (${otherOpenGoals.length})`,
          `<p class="muted" style="font-size:12px;margin:0 0 8px">Numbering matches the prover stack (goal 1 is above).</p><ol class="goal-stack secondary" start="2">${otherOpenGoals
            .map((g) => `<li class="goal-line"><span class="turnstile">⊢</span> ${escapeHtml(g)}</li>`)
            .join("")}</ol>`,
        )
      : "";

  const goalTitle = openGoals.length > 1 ? "Goal (focused)" : "Goal";
  const goal = section(goalTitle, `<p class="goal">⊢ ${escapeHtml(goalFriendly)}</p>`);
  const head = section(
    "Goal parameters",
    listItems(ps.headContext.map((c) => ({ label: c.name, value: c.type }))),
  );

  const term = section(
    "Term context (at cursor)",
    `<p class="muted" style="font-size:12px;margin:0 0 8px">Binders along the path into a <code>Def</code>/<code>Qed</code> proof term, or into a tactic argument you are editing.</p>${listItems(ps.termContext.map((c) => ({ label: c.name, value: c.type })))}`,
  );

  const envList = ps.environment ?? [];
  const envBlock =
    envList.length === 0
      ? ""
      : `<details class="fold"><summary>Global environment (${envList.length} names)</summary>${listItems(
          envList.map((e) => ({ label: `${e.name} (${e.kind})`, value: e.type })),
        )}</details>`;

  const metaList = ps.metas ?? [];
  const openMetas = metaList.filter((m) => m.solution == null);
  const solvedMetas = metaList.filter((m) => m.solution != null);
  const renderMeta = (m: { id: number; type: string | null; solution: string | null; context: number[] }) => {
    const short = compactMetaLabel(m.id);
    const ty = m.type != null ? renderFriendlyTerm(m.type, ps.hyps) : "(unknown type)";
    const sol = m.solution != null ? renderFriendlyTerm(m.solution, ps.hyps) : null;
    const ctxNames = friendlyCtxNames(m.context ?? [], ps.hyps);
    const ctx =
      ctxNames.length > 0
        ? `<div class="meta-ctx"><span class="muted">context:</span> ${escapeHtml(ctxNames.join(", "))}</div>`
        : "";
    const solved =
      sol != null
        ? `<div class="meta-sol"><span class="muted">solution:</span> ${escapeHtml(sol)}</div>`
        : "";
    return `<li class="mono meta-item"><div><span class="name">?${escapeHtml(short)}</span> <span class="muted">(#${m.id})</span></div><div><span class="muted">type:</span> ${escapeHtml(ty)}</div>${solved}${ctx}</li>`;
  };
  const metaBlock =
    metaList.length === 0
      ? ""
      : `<details class="fold"><summary>Metas (${metaList.length}) - open ${openMetas.length}, solved ${solvedMetas.length}</summary>
          ${openMetas.length > 0 ? `<h3 class="meta-heading">Open</h3><ul>${openMetas.map(renderMeta).join("")}</ul>` : `<p class="muted">No open metas.</p>`}
          ${solvedMetas.length > 0 ? `<details class="fold nested"><summary>Solved (${solvedMetas.length})</summary><ul>${solvedMetas.map(renderMeta).join("")}</ul></details>` : ""}
        </details>`;

  const hypsBody = listItems(
    ps.hyps.map((h) => ({
      label: h.name,
      value: renderFriendlyTerm(h.type, ps.hyps),
    })),
  );
  const hyps = `<section class="block goal-hyps"><h2>Goal hypotheses</h2>${hypsBody}</section>`;

  const tacticSteps = ps.tacticSteps ?? [];
  const applied = Math.max(0, Math.min(ps.tacticsApplied ?? 0, tacticSteps.length));
  const tacticBlock =
    tacticSteps.length === 0
      ? section("Tactic progress", `<p class="muted">(none)</p>`)
      : `<section class="block"><h2>Tactic progress</h2><p class="muted">Executed ${applied}/${tacticSteps.length}</p><ul class="tactic-list">${tacticSteps
          .map((s, i) => {
            const args = s.args.length > 0 ? ` ${s.args.join(" ")}` : "";
            const isExecuted = i < applied;
            const afterPretty = s.goalsAfter.map((g) => renderFriendlyTerm(g, ps.hyps));
            const after =
              s.goalsAfter.length === 0
                ? "(solved)"
                : afterPretty.length === 1
                  ? afterPretty[0]
                  : `<ol class="tactic-subgoals">${afterPretty
                      .map((g) => `<li class="goal">⊢ ${escapeHtml(g)}</li>`)
                      .join("")}</ol>`;
            const cursorTag = s.atCursor ? ` <span class="cursor-pill">cursor</span>` : "";
            const stateClass = isExecuted ? "tactic-executed" : "tactic-remaining";
            const stateText = isExecuted ? "executed" : "remaining";
            const detail = isExecuted
              ? `<div class="tactic-after"><span class="muted">after:</span> ${
                  typeof after === "string" && after.startsWith("<ol")
                    ? after
                    : escapeHtml(after)
                }</div>`
              : `<div class="tactic-after muted">after: (pending)</div>`;
            return `<li class="tactic-item ${stateClass}"><div><span class="name">[${s.index}] ${escapeHtml(s.name)}${escapeHtml(args)}</span>${cursorTag}</div><div class="tactic-meta"><span class="muted">status:</span> ${escapeHtml(s.status)} <span class="tactic-state">${stateText}</span></div>${detail}</li>`;
          })
          .join("")}</ul></section>`;

  return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
    body { font-family: var(--vscode-font-family); font-size: 13px; color: var(--vscode-foreground); padding: 12px; }
    h2 { font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; margin: 16px 0 8px; color: var(--vscode-descriptionForeground); }
    .block:first-child h2 { margin-top: 0; }
    .goal { font-family: var(--vscode-editor-font-family); font-size: 13px; color: var(--vscode-terminal-ansiGreen); }
    .goal-stack { margin: 8px 0 0; padding-left: 22px; }
    .goal-stack.secondary { margin-top: 4px; }
    .goal-line { margin: 6px 0; padding: 6px 8px; border-radius: 6px; border: 1px solid var(--vscode-panel-border); font-family: var(--vscode-editor-font-family); font-size: 12px; color: var(--vscode-terminal-ansiGreen); }
    .turnstile { margin-right: 6px; opacity: 0.85; }
    .tactic-subgoals { margin: 6px 0 0; padding-left: 20px; }
    .tactic-subgoals li { color: var(--vscode-terminal-ansiGreen); }
    .goal-hyps li { color: var(--vscode-terminal-ansiYellow); }
    .goal-hyps .name { color: var(--vscode-terminal-ansiYellow); }
    .name { font-weight: 600; }
    ul { padding-left: 18px; margin: 8px 0; }
    li { margin: 4px 0; font-family: var(--vscode-editor-font-family); font-size: 12px; }
    .muted { opacity: 0.8; }
    details.fold { margin: 12px 0; }
    details.fold summary { cursor: pointer; font-size: 11px; text-transform: uppercase; letter-spacing: 0.06em; color: var(--vscode-descriptionForeground); margin-bottom: 8px; }
    li.mono { font-family: var(--vscode-editor-font-family); font-size: 12px; margin: 4px 0; }
    .tactic-list { list-style: none; padding-left: 0; }
    .tactic-item { border: 1px solid var(--vscode-panel-border); border-radius: 6px; padding: 8px; margin: 8px 0; }
    .tactic-executed { background: color-mix(in srgb, var(--vscode-terminal-ansiGreen) 12%, transparent); }
    .tactic-remaining { opacity: 0.7; background: color-mix(in srgb, var(--vscode-editor-foreground) 6%, transparent); }
    .tactic-meta { margin-top: 2px; }
    .tactic-state { margin-left: 8px; padding: 1px 6px; border-radius: 999px; font-size: 11px; border: 1px solid var(--vscode-panel-border); }
    .cursor-pill { margin-left: 8px; padding: 1px 6px; border-radius: 999px; background: var(--vscode-textBlockQuote-background); font-size: 11px; }
    .tactic-after { margin-top: 4px; }
    .meta-heading { margin: 8px 0 4px; font-size: 11px; text-transform: uppercase; letter-spacing: 0.05em; color: var(--vscode-descriptionForeground); }
    .meta-item { border: 1px solid var(--vscode-panel-border); border-radius: 6px; padding: 6px; margin: 6px 0; }
    .meta-sol { margin-top: 2px; color: var(--vscode-terminal-ansiGreen); }
    .meta-ctx { margin-top: 2px; }
    details.fold.nested { margin-top: 8px; }

  </style></head><body>
    ${declBlock ?? ""}
    ${envBlock}
    ${metaBlock}
    ${head}
    ${hyps}
    ${goal}
    ${reduced}
    ${otherGoalsBlock}
    ${term}
    ${tacticBlock}
  </body></html>`;
}
