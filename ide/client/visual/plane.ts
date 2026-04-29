import type { ModifierSection, ToolSection } from "./section";
import type { LocationInput, ToolResult } from "./tools";
import type { Construction } from "./constructions";

export type PlaneView = {
  scale: number;
  offsetX: number;
  offsetY: number;
};

export type PlanePointer = {
  active: boolean;
  lastX: number;
  lastY: number;
};

export class Plane {
  private readonly canvas: HTMLCanvasElement;

  private readonly tools: ToolSection;
  private readonly modifiers: ModifierSection;

  private readonly constructions: Construction[] = [];

  private readonly view: PlaneView = {
    scale: 60,
    offsetX: 0,
    offsetY: 0,
  };

  private readonly pointer: PlanePointer = {
    active: false,
    lastX: 0,
    lastY: 0,
  };

  constructor(canvas: HTMLCanvasElement, tools: ToolSection, modifiers: ModifierSection) {
    this.canvas = canvas;
    this.tools = tools;
    this.modifiers = modifiers;
  }

  mount(): void {
    this.draw();

    window.addEventListener("resize", this.draw);
    this.canvas.addEventListener("pointerdown", this.onPointerDown);
    this.canvas.addEventListener("pointermove", this.onPointerMove);
    this.canvas.addEventListener("pointerup", this.onPointerEnd);
    this.canvas.addEventListener("pointercancel", this.onPointerEnd);
    this.canvas.addEventListener("wheel", this.onWheel, { passive: false });

    this.canvas.style.cursor = "grab";
  }

  private readonly draw = (): void => {
    const rect = this.canvas.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    const width = Math.max(1, Math.floor(rect.width * dpr));
    const height = Math.max(1, Math.floor(rect.height * dpr));

    if (this.canvas.width !== width || this.canvas.height !== height) {
      this.canvas.width = width;
      this.canvas.height = height;
    }

    const ctx = this.canvas.getContext("2d");
    if (!ctx) return;

    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, width, height);
    ctx.scale(dpr, dpr);

    const w = rect.width;
    const h = rect.height;
    const originX = w / 2 + this.view.offsetX;
    const originY = h / 2 + this.view.offsetY;
    const gridStep = this.view.scale;

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

    for (const c of this.constructions) {
      c.render(ctx, this.view);
    }
  };

  private readonly zoomAtPoint = (clientX: number, clientY: number, deltaScale: number): void => {
    const rect = this.canvas.getBoundingClientRect();
    const localX = clientX - rect.left;
    const localY = clientY - rect.top;

    const nextScale = Math.min(240, Math.max(12, this.view.scale * deltaScale));
    const scaleRatio = nextScale / this.view.scale;

    this.view.offsetX = localX - (localX - this.view.offsetX) * scaleRatio;
    this.view.offsetY = localY - (localY - this.view.offsetY) * scaleRatio;
    this.view.scale = nextScale;

    this.draw();
  };

  private readonly onPointerDown = (event: PointerEvent): void => {
    const activeTool = this.tools.activeTool;

    if (!activeTool) {
      this.pointer.active = true;
      this.pointer.lastX = event.clientX;
      this.pointer.lastY = event.clientY;
      this.canvas.setPointerCapture(event.pointerId);
      this.canvas.style.cursor = "grabbing";

      return;
    }

    const rect = this.canvas.getBoundingClientRect();
    const localX = event.clientX - rect.left;
    const localY = event.clientY - rect.top;

    const worldX = (localX - (rect.width / 2 + this.view.offsetX)) / this.view.scale;
    const worldY = (localY - (rect.height / 2 + this.view.offsetY)) / this.view.scale;

    const input: LocationInput = { kind: "location", x: worldX, y: worldY };

    const result: ToolResult = activeTool.activate(input);
    switch (result.kind) {
      case "construction":
        this.constructions.push(result.construction);
        this.draw();
        break;
      case "failure":
        this.tools.cancel();
        break;
      case "continue":
        break;
      default:
        throw result satisfies never;
    }
  };

  private readonly onPointerMove = (event: PointerEvent): void => {
    if (!this.pointer.active) return;

    const dx = event.clientX - this.pointer.lastX;
    const dy = event.clientY - this.pointer.lastY;

    this.pointer.lastX = event.clientX;
    this.pointer.lastY = event.clientY;
    this.view.offsetX += dx;
    this.view.offsetY += dy;

    this.draw();
  };

  private readonly onPointerEnd = (event: PointerEvent): void => {
    if (!this.pointer.active) return;

    this.pointer.active = false;
    this.canvas.releasePointerCapture(event.pointerId);
    this.canvas.style.cursor = "grab";
  };

  private readonly onWheel = (event: WheelEvent): void => {
    event.preventDefault();
    const zoomFactor = event.deltaY < 0 ? 1.12 : 0.89;
    this.zoomAtPoint(event.clientX, event.clientY, zoomFactor);
  };
}
