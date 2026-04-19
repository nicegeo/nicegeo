import * as vscode from "vscode";
import * as path from "path";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

import { NiceGeoOutput } from "./core/output";
import { NiceGeoStatusBar } from "./core/status";
import type { ProofStateAtPayload } from "./core/proofStatePanel";
import { ProofStateSidebarWebviewProvider } from "./core/proofStateSidebarWebview";

type ServerStatusPayload =
  | { kind: "idle" }
  | { kind: "checking"; detail?: string }
  | { kind: "ok" }
  | { kind: "issues"; count: number };

const STATUS_NOTIFICATION = "nicegeo/status";
const RUN_DIAGNOSTICS_NOTIFICATION = "nicegeo/runDiagnostics";
const PROOF_STATE_AT_REQUEST = "nicegeo/proofStateAt";
/** Workspace flag: when true, proof state commands and follow-cursor updates are allowed. */
const PROOF_MODE_WORKSPACE_KEY = "proofModeEnabled";

export function activate(context: vscode.ExtensionContext) {
  const output = new NiceGeoOutput();
  const status = new NiceGeoStatusBar("nicegeo.diagnostics.showOutput");
  status.init();

  const serverModule = context.asAbsolutePath(path.join("server", "out", "server.js"));
  const serverOptions: ServerOptions = {
    run: { module: serverModule, transport: TransportKind.stdio },
    debug: { module: serverModule, transport: TransportKind.stdio },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "nicegeo" }],
    synchronize: {
      configurationSection: "nicegeo",
    },
  };

  const client = new LanguageClient("nicegeo", "NiceGeo Language Server", serverOptions, clientOptions);
  context.subscriptions.push(output, status, client);
  const proofSidebarWebview = new ProofStateSidebarWebviewProvider();
  context.subscriptions.push(
    vscode.window.registerWebviewViewProvider(
      "nicegeoProofStateWebview",
      proofSidebarWebview,
    ),
  );

  const proofModeStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 99);
  proofModeStatusBar.command = "nicegeo.proofMode.toggle";
  context.subscriptions.push(proofModeStatusBar);

  const syncProofModeContext = (enabled: boolean) => {
    void vscode.commands.executeCommand("setContext", "nicegeo.proofMode", enabled);
  };

  let proofModeEnabled = context.workspaceState.get<boolean>(PROOF_MODE_WORKSPACE_KEY) ?? false;
  proofSidebarWebview.setProofModeEnabled(proofModeEnabled);
  syncProofModeContext(proofModeEnabled);
  const refreshProofModeStatusBar = () => {
    proofModeStatusBar.text = proofModeEnabled
      ? "$(checklist) NiceGeo proof: ON"
      : "$(circle-slash) NiceGeo proof: OFF";
    proofModeStatusBar.tooltip = proofModeEnabled
      ? "NiceGeo proof mode is on (click to toggle)"
      : "NiceGeo proof mode is off (click to toggle)";
    proofModeStatusBar.show();
  };
  refreshProofModeStatusBar();

  const setProofMode = async (enabled: boolean) => {
    proofModeEnabled = enabled;
    await context.workspaceState.update(PROOF_MODE_WORKSPACE_KEY, enabled);
    proofSidebarWebview.setProofModeEnabled(enabled);
    syncProofModeContext(enabled);
    refreshProofModeStatusBar();
  };

  const clientStart = client.start();

  let proofStateFollowDebounce: ReturnType<typeof setTimeout> | undefined;
  const refreshProofStateAtCursor = async (
    editor: vscode.TextEditor,
    focusPanel: boolean,
    quiet: boolean,
  ) => {
    if (!proofModeEnabled) {
      if (!quiet) {
        void vscode.window.showWarningMessage(
          "Turn on NiceGeo proof mode first (command: NiceGeo: Enter Proof Mode).",
        );
      }
      return;
    }
    if (editor.document.languageId !== "nicegeo") return;
    await clientStart;
    const pos = editor.selection.active;
    try {
      const result = await client.sendRequest<ProofStateAtPayload>(PROOF_STATE_AT_REQUEST, {
        uri: editor.document.uri.toString(),
        line: pos.line,
        col: pos.character,
      });
      proofSidebarWebview.setData(result);
      if (focusPanel) {
        void vscode.commands.executeCommand("nicegeoProofStateWebview.focus");
      }
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      if (quiet) {
        output.appendLine(`[nicegeo] proof state (follow-cursor): ${msg}`);
      } else {
        void vscode.window.showErrorMessage(`NiceGeo proof state: ${msg}`);
      }
    }
  };

  const scheduleProofStateFollowCursor = () => {
    if (!proofModeEnabled) return;
    if (!proofSidebarWebview.isViewVisible()) return;
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== "nicegeo") return;
    const cfg = vscode.workspace.getConfiguration("nicegeo");
    if (!cfg.get<boolean>("proofState.followCursor", true)) return;
    const ms = cfg.get<number>("proofState.followCursorDebounceMs", 300);
    if (proofStateFollowDebounce !== undefined) {
      clearTimeout(proofStateFollowDebounce);
    }
    proofStateFollowDebounce = setTimeout(() => {
      proofStateFollowDebounce = undefined;
      void refreshProofStateAtCursor(editor, false, true);
    }, ms);
  };

  output.appendLine("[nicegeo] extension activated");
  output.appendLine(`[nicegeo] starting language server: ${serverModule}`);

  client.onNotification(STATUS_NOTIFICATION, (payload: ServerStatusPayload) => {
    status.set(payload);
  });

  context.subscriptions.push(
    vscode.commands.registerCommand("nicegeo.diagnostics.showOutput", () => {
      output.show(true);
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("nicegeo.diagnostics.run", async () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor) return;
      if (editor.document.languageId !== "nicegeo") return;
      await clientStart;
      client.sendNotification(RUN_DIAGNOSTICS_NOTIFICATION, { uri: editor.document.uri.toString() });
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("nicegeo.proofMode.enter", async () => {
      await setProofMode(true);
      const editor = vscode.window.activeTextEditor;
      if (editor && editor.document.languageId === "nicegeo") {
        await refreshProofStateAtCursor(editor, true, false);
      } else {
        void vscode.window.showInformationMessage(
          "NiceGeo proof mode is on. Open a .ncg file to see live proof state.",
        );
      }
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("nicegeo.proofMode.exit", async () => {
      if (proofStateFollowDebounce !== undefined) {
        clearTimeout(proofStateFollowDebounce);
        proofStateFollowDebounce = undefined;
      }
      await setProofMode(false);
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("nicegeo.proofMode.toggle", async () => {
      if (proofModeEnabled) {
        await vscode.commands.executeCommand("nicegeo.proofMode.exit");
      } else {
        await vscode.commands.executeCommand("nicegeo.proofMode.enter");
      }
    }),
  );


  context.subscriptions.push(
    vscode.window.onDidChangeTextEditorSelection((e) => {
      if (e.textEditor === vscode.window.activeTextEditor) {
        scheduleProofStateFollowCursor();
      }
    }),
  );

  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      scheduleProofStateFollowCursor();
      if (proofModeEnabled && editor && editor.document.languageId === "nicegeo") {
        void refreshProofStateAtCursor(editor, true, true);
      }
    }),
  );
}

export function deactivate() {}
