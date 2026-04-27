/// <reference types="vscode-webview" />

import "@vscode-elements/elements";
import { Plane } from "./plane.js";
import { Section, Tool } from "./tools.js";

const canvas = document.getElementById("planeCanvas") as HTMLCanvasElement | null;
const toolbar = document.getElementById("toolbar") as HTMLDivElement | null;

const TOOLS = [
  new Tool({ id: "point", label: "Point", icon: "circle-filled", action: () => {} }),
  new Tool({ id: "line", label: "Line", icon: "arrow-both", action: () => {} }),
  new Tool({ id: "circle", label: "Circle", icon: "circle-large", action: () => {} }),
];

const MODIFIERS = [new Tool({ id: "distinct", label: "Distinct", icon: "diff-removed", action: () => {} })];

window.addEventListener("DOMContentLoaded", () => {
  if (!canvas || !toolbar) return;

  const plane = new Plane(canvas);
  plane.mount();

  const toolsSection = new Section({
    title: "Tools",
    className: "toolSection",
    tools: TOOLS,
    activeTool: TOOLS[0],
  });

  const modifiersSection = new Section({
    title: "Modifiers",
    className: "modifierSection",
    tools: MODIFIERS,
    isModifier: true,
  });

  toolbar.replaceChildren(toolsSection.render(), modifiersSection.render());
});
