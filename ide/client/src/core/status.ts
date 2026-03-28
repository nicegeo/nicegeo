import * as vscode from "vscode";

export type NiceGeoStatusState =
  | { kind: "idle" }
  | { kind: "checking"; detail?: string }
  | { kind: "ok" }
  | { kind: "issues"; count: number };

export class NiceGeoStatusBar {
  private readonly item = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);

  constructor(private readonly onClickCommand: string) {}

  init() {
    this.item.command = this.onClickCommand;
    this.set({ kind: "idle" });
    this.item.show();
  }

  dispose() {
    this.item.dispose();
  }

  set(state: NiceGeoStatusState) {
    switch (state.kind) {
      case "idle":
        this.item.text = "NiceGeo: idle";
        this.item.tooltip = "NiceGeo diagnostics";
        return;
      case "checking":
        this.item.text = "$(sync~spin) NiceGeo: checking";
        this.item.tooltip = state.detail ?? "Running NiceGeo diagnostics";
        return;
      case "ok":
        this.item.text = "NiceGeo: ok";
        this.item.tooltip = "No errors";
        return;
      case "issues":
        this.item.text = `NiceGeo: ${state.count} issue${state.count === 1 ? "" : "s"}`;
        this.item.tooltip = "Click to open diagnostics output";
        return;
    }
  }
}

