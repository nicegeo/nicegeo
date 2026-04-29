import { LocalPoint, PlaneView } from './coordinates';

/**
 * Abstract base class for geometric constructions
 */
export abstract class Construction {
  /** Name/label for this construction */
  public name: string;

  constructor(name: string) {
    this.name = name;
  }

  /**
   * Renders this construction on the given canvas context
   */
  abstract render(ctx: CanvasRenderingContext2D, planeView: PlaneView): void;

  /**
   * Validates the construction
   */
  abstract validate(): boolean;
}

/**
 * A Point construction
 */
export class Point extends Construction {
  private _pos: LocalPoint;

  constructor(name: string, x: number, y: number) {
    super(name);
    this._pos = new LocalPoint(x, y);
  }

  get x(): number {
    return this._pos.x;
  }

  get y(): number {
    return this._pos.y;
  }

  setCoordinates(x: number, y: number): void {
    this._pos = new LocalPoint(x, y);
  }

  override render(ctx: CanvasRenderingContext2D, view: PlaneView): void {
    const { x: canvasX, y: canvasY } = this._pos.toCanvas(ctx.canvas, view);

    const radius = 12;
    const color = getComputedStyle(document.body).getPropertyValue("--vscode-button-background");

    ctx.fillStyle = color;

    ctx.globalAlpha = 0.5;
    ctx.beginPath();
    ctx.arc(canvasX, canvasY, radius, 0, 2 * Math.PI);
    ctx.fill();
    ctx.globalAlpha = 1;

    ctx.beginPath();
    ctx.arc(canvasX, canvasY, radius / 2, 0, 2 * Math.PI);
    ctx.fill();
  }

  override validate(): boolean {
    return true;
  }
}
