/// <reference types="vscode-webview" />

import "@vscode-elements/elements";

type ExtensionMessage = {
  type: "set-status";
  text: string;
};

const vscode = acquireVsCodeApi();

const setStatus = (text: string): void => {
  const status = document.getElementById("statusText");
  if (!status) return;
  status.textContent = text;
};

window.addEventListener("message", (event: MessageEvent<ExtensionMessage>) => {
  if (event.data.type === "set-status") {
    setStatus(event.data.text);
  }
});

window.addEventListener("DOMContentLoaded", () => {
  const pingButton = document.getElementById("pingButton");
  pingButton?.addEventListener("click", () => {
    vscode.postMessage({ type: "ping" });
  });

  vscode.postMessage({ type: "ready" });
});
