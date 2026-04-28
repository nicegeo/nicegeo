import { PlaneView } from './plane';

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
   * Abstract method that must be implemented by subclasses
   * Renders this construction on the given canvas context
   */
  abstract render(ctx: CanvasRenderingContext2D, planeView: PlaneView): void;

  /**
   * Abstract method that must be implemented by subclasses
   * Validates the construction
   */
  abstract validate(): boolean;
}

/**
 * A Point construction
 */
export class Point extends Construction {
  /** X coordinate */
  private _x: number;

  /** Y coordinate */
  private _y: number;

  constructor(name: string, x: number, y: number) {
    super(name);
    this._x = x;
    this._y = y;
  }

  /**
   * Get the X coordinate
   */
  get x(): number {
    return this._x;
  }

  /**
   * Get the Y coordinate
   */
  get y(): number {
    return this._y;
  }

  /**
   * Set the coordinates
   */
  setCoordinates(x: number, y: number): void {
    this._x = x;
    this._y = y;
  }

  /**
   * Render the point on the canvas
   */
  override render(ctx: CanvasRenderingContext2D, view: PlaneView): void {
    const rect = ctx.canvas.getBoundingClientRect();
    const canvasX = rect.width / 2 + view.offsetX + this._x * view.scale;
    const canvasY = rect.height / 2 + view.offsetY + this._y * view.scale;

    const radius = 4;
    const lineWidth = 2;

    // Draw the point circle
    ctx.strokeStyle = '#ff6b6b';
    ctx.lineWidth = lineWidth;
    ctx.beginPath();
    ctx.arc(canvasX, canvasY, radius, 0, 2 * Math.PI);
    ctx.stroke();

    // Draw a filled center
    ctx.fillStyle = '#ff6b6b';
    ctx.beginPath();
    ctx.arc(canvasX, canvasY, radius / 2, 0, 2 * Math.PI);
    ctx.fill();
  }

  /**
   * Validate the point coordinates
   */
  override validate(): boolean {
    return true;
  }
}
