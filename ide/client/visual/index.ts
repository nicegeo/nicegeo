/// <reference types="vscode-webview" />

import "@vscode-elements/elements";
import { Plane } from "./plane.js";

const canvas = document.getElementById("planeCanvas") as HTMLCanvasElement | null;
const toolbar = document.getElementById("toolbar") as HTMLDivElement | null;

type ToolButtonDefinition = {
  id: string;
  label: string;
  icon: string;
  action: () => void;
};

const TOOLS: ToolButtonDefinition[] = [
  { id: "point", label: "Point", icon: "circle-filled", action: () => {} },
  { id: "line", label: "Line", icon: "arrow-both", action: () => {} },
  { id: "circle", label: "Circle", icon: "circle-large", action: () => {} },
];

const MODIFIERS: ToolButtonDefinition[] = [
  { id: "distinct", label: "Distinct", icon: "diff-removed", action: () => {} },
];

let activeToolId = TOOLS[0].id;

const updateActiveToolButtons = (): void => {
  for (const tool of TOOLS) {
    const button = document.getElementById(`toolButton-${tool.id}`)!;
    button.classList.toggle("toolButtonActive", tool.id === activeToolId);
  }
};

const buildToolButton = (
  { id, label, icon, action }: ToolButtonDefinition,
  isModifier: boolean,
): HTMLElement => {
  const button = document.createElement("vscode-button");
  button.id = `toolButton-${id}`;
  button.className = "toolButton";
  button.title = label;
  button.icon = icon;
  
  button.addEventListener("click", () => {
    if (!isModifier) {
      activeToolId = id;
      updateActiveToolButtons();
    }

    action();
  });

  return button;
};

const buildGroup = (
  buttons: ToolButtonDefinition[],
  isModifier: boolean,
): HTMLElement => {
  const group = document.createElement("div");
  group.className = "group";
  group.append(...buttons.map((button) => buildToolButton(button, isModifier)));
  return group;
};

const buildSection = (
  title: string,
  buttons: ToolButtonDefinition[],
  sectionClassName: string,
  isModifier: boolean,
): HTMLElement => {
  const section = document.createElement("section");
  section.className = sectionClassName;

  const titleElement = document.createElement("span");
  titleElement.className = "sectionTitle";
  titleElement.textContent = title;

  const group = buildGroup(buttons, isModifier);
  section.append(titleElement, group);
  return section;
};

const renderToolButtons = (): void => {
  if (!toolbar) return;

  const toolsGroup = buildSection("Tools", TOOLS, "toolSection", false);
  const modifiersGroup = buildSection("Modifiers", MODIFIERS, "modifierSection", true);

  toolbar.replaceChildren(toolsGroup, modifiersGroup);
  updateActiveToolButtons();
};

window.addEventListener("DOMContentLoaded", () => {
  if (!canvas) return;

  const plane = new Plane(canvas);

  renderToolButtons();
  plane.mount();
});
