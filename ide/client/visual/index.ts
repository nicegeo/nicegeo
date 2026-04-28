/// <reference types="vscode-webview" />

import "@vscode-elements/elements";
import { Plane } from "./plane.js";
import { CircleTool, DistinctModifier, LineTool, PointTool } from "./tools.js";
import { ModifierSection, ToolSection } from "./section.js";

const canvas = document.getElementById("planeCanvas") as HTMLCanvasElement | null;
const toolbar = document.getElementById("toolbar") as HTMLDivElement | null;

window.addEventListener("DOMContentLoaded", () => {
  if (!canvas || !toolbar) return;

  const plane = new Plane(canvas);
  plane.mount();

  const toolSection = new ToolSection({
    title: "Tools",
    className: "toolSection",
    items: [PointTool, LineTool, CircleTool],
  });

  const modifierSection = new ModifierSection({
    title: "Modifiers",
    className: "modifierSection",
    items: [DistinctModifier],
  });

  toolbar.replaceChildren(toolSection.render(), modifierSection.render());
});
