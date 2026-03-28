import * as vscode from "vscode";

export class NiceGeoOutput {
  private readonly channel = vscode.window.createOutputChannel("NiceGeo Diagnostics");

  dispose() {
    this.channel.dispose();
  }

  show(preserveFocus = true) {
    this.channel.show(preserveFocus);
  }

  appendLine(line: string) {
    this.channel.appendLine(line);
  }
}

