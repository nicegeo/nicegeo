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
import { showProofStatePanel, type ProofStateAtPayload } from "./core/proofStatePanel";

type ServerStatusPayload =
  | { kind: "idle" }
  | { kind: "checking"; detail?: string }
  | { kind: "ok" }
  | { kind: "issues"; count: number };

const STATUS_NOTIFICATION = "nicegeo/status";
const RUN_DIAGNOSTICS_NOTIFICATION = "nicegeo/runDiagnostics";
const PROOF_STATE_AT_REQUEST = "nicegeo/proofStateAt";

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

  output.appendLine("[nicegeo] extension activated");
  output.appendLine(`[nicegeo] starting language server: ${serverModule}`);

  client.onNotification(STATUS_NOTIFICATION, (payload: ServerStatusPayload) => {
    status.set(payload);
  });

  const clientStart = client.start();

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
    vscode.commands.registerCommand("nicegeo.proofState.showPanel", async () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        void vscode.window.showWarningMessage("No active editor.");
        return;
      }
      if (editor.document.languageId !== "nicegeo") {
        void vscode.window.showWarningMessage("Open a NiceGeo (.ncg) file to show proof state.");
        return;
      }
      await clientStart;
      const pos = editor.selection.active;
      try {
        const result = await client.sendRequest<ProofStateAtPayload>(PROOF_STATE_AT_REQUEST, {
          uri: editor.document.uri.toString(),
          line: pos.line,
          col: pos.character,
        });
        showProofStatePanel(result);
      } catch (e) {
        const msg = e instanceof Error ? e.message : String(e);
        void vscode.window.showErrorMessage(`NiceGeo proof state: ${msg}`);
      }
    }),
  );
}

export function deactivate() {}
