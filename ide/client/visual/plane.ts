import type { ModifierSection, ToolSection } from "./section";
import type { LocationInput, ToolResult } from "./tools";
import type { Construction } from "./constructions";
import type { LocalPoint, PlaneView } from "./coordinates";
import { CanvasPoint, ClientPoint } from "./coordinates";

export type PlanePointer = {
  active: boolean;
  point?: ClientPoint;
};

export class Plane {
  private readonly canvas: HTMLCanvasElement;

  private readonly tools: ToolSection;
  private readonly modifiers: ModifierSection;

  private readonly constructions: Construction[] = [];
  private readonly hovered: Set<Construction> = new Set();

  private readonly view: PlaneView = {
    scale: 60,
    offsetX: 0,
    offsetY: 0,
  };

  private readonly pointer: PlanePointer = {
    active: false,
    point: undefined,
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
    this.canvas.addEventListener("pointerleave", this.onPointerLeave);
    this.canvas.addEventListener("wheel", this.onWheel, { passive: false });

    this.canvas.style.cursor = "grab";
  }

  private updateHovers(): void {
    this.hovered.clear();

    if (!this.pointer.point) return;

    for (const c of this.constructions) {
      if (c.isHovering(this.pointer.point, this.canvas, this.view)) {
        this.hovered.add(c);
      }
    }
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

    const { x: originX, y: originY } = CanvasPoint.origin(this.canvas, this.view);

    const gridStep = this.view.scale;

    const style = getComputedStyle(document.body);
    const backgroundColor = style.backgroundColor;
    const gridColor = style.color;

    ctx.fillStyle = backgroundColor;
    ctx.fillRect(0, 0, w, h);

    ctx.lineWidth = 1;
    ctx.strokeStyle = gridColor;

    ctx.globalAlpha = 0.85;

    const startX = originX % gridStep;
    const startY = originY % gridStep;

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
      c.render(ctx, this.view, this.hovered.has(c));
    }
  };

  private readonly onPointerDown = (event: PointerEvent): void => {
    this.pointer.point = new ClientPoint(event.clientX, event.clientY);
    this.updateHovers();
    
    const activeTool = this.tools.activeTool;

    if (!activeTool) {
      this.pointer.active = true;
      this.canvas.setPointerCapture(event.pointerId);
      this.canvas.style.cursor = "grabbing";

      return;
    }

    const input: LocationInput = { kind: "location", point: this.pointer.point.toLocal(this.canvas, this.view) };

    const result: ToolResult = activeTool.activate(input);
    switch (result.kind) {
      case "construction":
        this.constructions.push(result.construction);
        break;
      case "failure":
        this.tools.cancel();
        break;
      case "continue":
        break;
      default:
        throw result satisfies never;
    }
    
    this.draw();
  };

  private readonly onPointerMove = (event: PointerEvent): void => {
    if (this.pointer.active && this.pointer.point) {
      const dx = event.clientX - this.pointer.point.x;
      const dy = event.clientY - this.pointer.point.y;

      if (this.hovered.size > 0) {
        for (const c of this.hovered) {
          c.move(dx / this.view.scale, dy / this.view.scale);
        }
      } else {
        this.view.offsetX += dx;
        this.view.offsetY += dy;
      }
    }

    this.pointer.point = new ClientPoint(event.clientX, event.clientY);
    this.updateHovers();

    this.draw();
  };

  private readonly onPointerEnd = (event: PointerEvent): void => {
    if (!this.pointer.active) return;

    this.pointer.active = false;
    this.canvas.releasePointerCapture(event.pointerId);
    this.canvas.style.cursor = "grab";
  };

  private readonly onPointerLeave = (): void => {
    this.pointer.point = undefined;
    this.updateHovers();

    this.draw();
  };

  private readonly onWheel = (event: WheelEvent): void => {
    event.preventDefault();

    const zoomFactor = event.deltaY < 0 ? 1.12 : 0.89;

    const canvasPoint = new ClientPoint(event.clientX, event.clientY).toCanvas(this.canvas);
    const nextScale = Math.min(240, Math.max(12, this.view.scale * zoomFactor));
    const scaleRatio = nextScale / this.view.scale;

    const center = CanvasPoint.center(this.canvas);

    this.view.offsetX *= scaleRatio;
    this.view.offsetY *= scaleRatio;

    this.view.offsetX += (canvasPoint.x - center.x) * (1 - scaleRatio);
    this.view.offsetY += (canvasPoint.y - center.y) * (1 - scaleRatio);

    this.view.scale = nextScale;

    this.draw();
  };
}
