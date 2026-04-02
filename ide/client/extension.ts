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

type ServerStatusPayload =
  | { kind: "idle" }
  | { kind: "checking"; detail?: string }
  | { kind: "ok" }
  | { kind: "issues"; count: number };

const STATUS_NOTIFICATION = "nicegeo/status";
const RUN_DIAGNOSTICS_NOTIFICATION = "nicegeo/runDiagnostics";

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
}

export function deactivate() {}
