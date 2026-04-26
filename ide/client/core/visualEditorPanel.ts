import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";

type VisualEditorMessage = { type: "ready" } | { type: "ping" };

export class VisualEditorPanel {
  private static panel: vscode.WebviewPanel | undefined;

  static open(context: vscode.ExtensionContext): void {
    if (VisualEditorPanel.panel) {
      VisualEditorPanel.panel.reveal(vscode.ViewColumn.Beside);
      return;
    }

    const panel = vscode.window.createWebviewPanel(
      "nicegeoVisualEditor",
      "NiceGeo Visual Editor",
      vscode.ViewColumn.Beside,
      {
        enableScripts: true,
        retainContextWhenHidden: true,
      },
    );

    panel.webview.html = VisualEditorPanel.getWebviewHtml(
      context,
      panel.webview,
    );

    panel.onDidDispose(() => {
      VisualEditorPanel.panel = undefined;
    });

    panel.webview.onDidReceiveMessage((msg: VisualEditorMessage) => {
      if (msg.type === "ready") {
        void panel.webview.postMessage({
          type: "set-status",
          text: "Visual editor connected.",
        });
      }
      if (msg.type === "ping") {
        void panel.webview.postMessage({
          type: "set-status",
          text: "Ping received by extension.",
        });
      }
    });

    VisualEditorPanel.panel = panel;
  }

  private static getWebviewHtml(
    context: vscode.ExtensionContext,
    webview: vscode.Webview,
  ): string {
    const htmlPath = path.join(context.extensionPath, "client", "visual", "index.html");
    const htmlTemplate = fs.readFileSync(htmlPath, "utf8");

    const styleUri = webview.asWebviewUri(
      vscode.Uri.joinPath(context.extensionUri, "client", "visual", "index.css"),
    );
    const webviewScriptUri = webview.asWebviewUri(
      vscode.Uri.joinPath(context.extensionUri, "out", "visual", "index.js"),
    );

    const nonce = VisualEditorPanel.getNonce();

    return htmlTemplate
      .replaceAll("{{cspSource}}", webview.cspSource)
      .replaceAll("{{nonce}}", nonce)
      .replaceAll("{{styleUri}}", styleUri.toString())
      .replaceAll("{{scriptUri}}", webviewScriptUri.toString());
  }

  private static getNonce(): string {
    const alphabet =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    let nonce = "";
    for (let index = 0; index < 32; index += 1) {
      nonce += alphabet.charAt(Math.floor(Math.random() * alphabet.length));
    }
    return nonce;
  }
}
