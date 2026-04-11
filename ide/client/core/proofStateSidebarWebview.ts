import * as vscode from "vscode";
import { buildProofStateHtml, type ProofStateAtPayload } from "./proofStatePanel";

export class ProofStateSidebarWebviewProvider implements vscode.WebviewViewProvider {
  private view: vscode.WebviewView | undefined;
  private latest: ProofStateAtPayload | undefined;

  resolveWebviewView(webviewView: vscode.WebviewView): void {
    this.view = webviewView;
    webviewView.webview.options = { enableScripts: false };
    webviewView.webview.html = this.latest
      ? buildProofStateHtml(this.latest)
      : this.placeholderHtml();
  }

  setData(data: ProofStateAtPayload): void {
    this.latest = data;
    if (this.view) {
      this.view.webview.html = buildProofStateHtml(data);
    }
  }

  private placeholderHtml(): string {
    return `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
      body { font-family: var(--vscode-font-family); font-size: 13px; color: var(--vscode-foreground); padding: 12px; }
      .muted { opacity: 0.75; }
    </style></head><body>
      <p class="muted">Run <strong>NiceGeo: Show Proof State</strong> to load proof state here.</p>
    </body></html>`;
  }
}
