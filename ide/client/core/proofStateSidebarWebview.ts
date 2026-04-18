import * as vscode from "vscode";
import { buildProofStateHtml, type ProofStateAtPayload } from "./proofStatePanel";

export class ProofStateSidebarWebviewProvider implements vscode.WebviewViewProvider {
  private view: vscode.WebviewView | undefined;
  private latest: ProofStateAtPayload | undefined;
  /** True while the sidebar webview is shown (not collapsed). */
  private viewVisible = false;
  /** When false, proof state queries are disabled and the sidebar shows an off-state message. */
  private proofModeEnabled = false;

  /** Used to avoid spawning `nicegeo-proofstate` on every cursor move when the panel is hidden. */
  isViewVisible(): boolean {
    return this.viewVisible;
  }

  isProofModeEnabled(): boolean {
    return this.proofModeEnabled;
  }

  /** Call when entering or exiting proof mode (persists in extension; this only updates UI). */
  setProofModeEnabled(enabled: boolean): void {
    this.proofModeEnabled = enabled;
    if (!enabled) {
      this.latest = undefined;
    }
    if (this.view) {
      this.view.webview.html = this.latest ? buildProofStateHtml(this.latest) : this.placeholderHtml();
    }
  }

  resolveWebviewView(webviewView: vscode.WebviewView): void {
    this.view = webviewView;
    webviewView.webview.options = { enableScripts: false };
    this.viewVisible = webviewView.visible;
    webviewView.onDidChangeVisibility(() => {
      this.viewVisible = webviewView.visible;
    });
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
    const base = `<!DOCTYPE html><html><head><meta charset="UTF-8"><style>
      body { font-family: var(--vscode-font-family); font-size: 13px; color: var(--vscode-foreground); padding: 12px; }
      .muted { opacity: 0.75; }
    </style></head><body>`;
    if (!this.proofModeEnabled) {
      return `${base}
      <p>Proof mode is <strong>off</strong>.</p>
      <p class="muted">Run <strong>NiceGeo: Enter Proof Mode</strong> to enable live proof state and cursor updates.</p>
    </body></html>`;
    }
    return `${base}
      <p class="muted">Proof mode is <strong>on</strong>. Move the cursor (with this sidebar visible) to load proof state.</p>
    </body></html>`;
  }
}
