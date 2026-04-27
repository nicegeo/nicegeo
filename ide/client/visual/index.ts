/// <reference types="vscode-webview" />

import "@vscode-elements/elements";

const canvas = document.getElementById("planeCanvas") as HTMLCanvasElement | null;
const toolbar = document.getElementById("toolbar") as HTMLDivElement | null;

const view = {
  scale: 40,
  offsetX: 0,
  offsetY: 0,
};

const pointer = {
  active: false,
  lastX: 0,
  lastY: 0,
};

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

const drawCoordinatePlane = (): void => {
  if (!canvas) return;

  const rect = canvas.getBoundingClientRect();
  const dpr = window.devicePixelRatio || 1;
  const width = Math.max(1, Math.floor(rect.width * dpr));
  const height = Math.max(1, Math.floor(rect.height * dpr));

  if (canvas.width !== width || canvas.height !== height) {
    canvas.width = width;
    canvas.height = height;
  }

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, width, height);
  ctx.scale(dpr, dpr);

  const w = rect.width;
  const h = rect.height;
  const originX = w / 2 + view.offsetX;
  const originY = h / 2 + view.offsetY;
  const gridStep = view.scale;

  const style = getComputedStyle(document.body);

  const backgroundColor = style.backgroundColor;
  const gridColor = style.color;

  ctx.fillStyle = backgroundColor;
  ctx.fillRect(0, 0, w, h);

  ctx.lineWidth = 1;
  ctx.strokeStyle = gridColor;
  ctx.globalAlpha = 0.85;

  const startX = ((originX % gridStep) + gridStep) % gridStep;
  const startY = ((originY % gridStep) + gridStep) % gridStep;

  for (let x = startX; x <= w; x += gridStep) {
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, h);
    ctx.stroke();
  }

  for (let y = startY; y <= h; y += gridStep) {
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
  }

  ctx.globalAlpha = 1;
};

const zoomAtPoint = (clientX: number, clientY: number, deltaScale: number): void => {
  if (!canvas) return;

  const rect = canvas.getBoundingClientRect();
  const localX = clientX - rect.left;
  const localY = clientY - rect.top;

  const nextScale = Math.min(240, Math.max(12, view.scale * deltaScale));
  const scaleRatio = nextScale / view.scale;

  view.offsetX = localX - (localX - view.offsetX) * scaleRatio;
  view.offsetY = localY - (localY - view.offsetY) * scaleRatio;
  view.scale = nextScale;
  drawCoordinatePlane();
};

window.addEventListener("DOMContentLoaded", () => {
  if (!canvas) return;

  renderToolButtons();
  drawCoordinatePlane();

  window.addEventListener("resize", drawCoordinatePlane);

  canvas.addEventListener("pointerdown", (event) => {
    pointer.active = true;
    pointer.lastX = event.clientX;
    pointer.lastY = event.clientY;
    canvas.setPointerCapture(event.pointerId);
    canvas.style.cursor = "grabbing";
  });

  canvas.addEventListener("pointermove", (event) => {
    if (!pointer.active) return;

    const dx = event.clientX - pointer.lastX;
    const dy = event.clientY - pointer.lastY;
    pointer.lastX = event.clientX;
    pointer.lastY = event.clientY;
    view.offsetX += dx;
    view.offsetY += dy;
    drawCoordinatePlane();
  });

  const endDrag = (event: PointerEvent) => {
    if (!pointer.active) return;
    pointer.active = false;
    canvas.releasePointerCapture(event.pointerId);
    canvas.style.cursor = "grab";
  };

  canvas.addEventListener("pointerup", endDrag);
  canvas.addEventListener("pointercancel", endDrag);

  canvas.addEventListener(
    "wheel",
    (event) => {
      event.preventDefault();
      const zoomFactor = event.deltaY < 0 ? 1.12 : 0.89;
      zoomAtPoint(event.clientX, event.clientY, zoomFactor);
    },
    { passive: false },
  );

  canvas.style.cursor = "grab";
});
