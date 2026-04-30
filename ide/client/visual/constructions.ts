import { ClientPoint, LocalPoint, PlaneView } from './coordinates';

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
   * @param ctx The canvas rendering context
   * @param planeView The current plane view
   * @param isHovered Whether this construction is currently hovered
   */
  abstract render(ctx: CanvasRenderingContext2D, planeView: PlaneView, isHovered: boolean): void;

  /**
   * Validates the construction
   */
  abstract validate(): boolean;

  /**
   * Moves the construction by the given delta in local coordinates
   */
  abstract move(deltaX: number, deltaY: number): void;

  /**
   * Checks if a given ClientPoint should be considered hovering over this construction
   */
  abstract isHovering(point: ClientPoint, canvas: HTMLCanvasElement, view: PlaneView): boolean;
}

/**
 * A Point construction
 */
export class Point extends Construction {
  private static radius = 12;

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

  override render(ctx: CanvasRenderingContext2D, view: PlaneView, isHovered: boolean): void {
    const { x: canvasX, y: canvasY } = this._pos.toCanvas(ctx.canvas, view);

    const color = getComputedStyle(document.body).getPropertyValue("--vscode-button-background");

    ctx.fillStyle = color;

    if (isHovered) {
      ctx.beginPath();
      ctx.arc(canvasX, canvasY, Point.radius, 0, 2 * Math.PI);
      ctx.fill();
    } else {
      ctx.globalAlpha = 0.5;
      ctx.beginPath();
      ctx.arc(canvasX, canvasY, Point.radius, 0, 2 * Math.PI);
      ctx.fill();
      ctx.globalAlpha = 1;

      ctx.beginPath();
      ctx.arc(canvasX, canvasY, Point.radius / 2, 0, 2 * Math.PI);
      ctx.fill();
    }
  }

  override validate(): boolean {
    return true;
  }

  override move(deltaX: number, deltaY: number): void {
    this._pos = new LocalPoint(this._pos.x + deltaX, this._pos.y + deltaY);
  }

  override isHovering(point: ClientPoint, canvas: HTMLCanvasElement, view: PlaneView): boolean {
    let canvasPointer = point.toCanvas(canvas);
    let canvasPos = this._pos.toCanvas(canvas, view);

    const distance = Math.sqrt(
      Math.pow(canvasPointer.x - canvasPos.x, 2) + Math.pow(canvasPointer.y - canvasPos.y, 2)
    );

    console.log(`Point: (${canvasPos.x}, ${canvasPos.y}), Pointer: (${canvasPointer.x}, ${canvasPointer.y}), Distance: ${distance}`);

    return distance <= Point.radius;
  }
}
