export interface PlaneView {
  scale: number;
  offsetX: number;
  offsetY: number;
};

export class ClientPoint {
  constructor(public x: number, public y: number) {}

  toCanvas(canvas: HTMLCanvasElement): CanvasPoint {
    const rect = canvas.getBoundingClientRect();
    return new CanvasPoint(this.x - rect.left, this.y - rect.top);
  }

  toLocal(canvas: HTMLCanvasElement, view: PlaneView): LocalPoint {
    return this.toCanvas(canvas).toLocal(canvas, view);
  }
}

export class CanvasPoint {
  constructor(public x: number, public y: number) {}

  static center(canvas: HTMLCanvasElement): CanvasPoint {
    const rect = canvas.getBoundingClientRect();
    return new CanvasPoint(rect.width / 2, rect.height / 2);
  }

  static origin(canvas: HTMLCanvasElement, view: PlaneView): CanvasPoint {
    const center = CanvasPoint.center(canvas);
    return new CanvasPoint(center.x + view.offsetX, center.y + view.offsetY);
  }

  toClient(canvas: HTMLCanvasElement): ClientPoint {
    const rect = canvas.getBoundingClientRect();
    return new ClientPoint(this.x + rect.left, this.y + rect.top);
  }

  toLocal(canvas: HTMLCanvasElement, view: PlaneView): LocalPoint {
    const origin = CanvasPoint.origin(canvas, view);
    return new LocalPoint(
      (this.x - origin.x) / view.scale,
      (this.y - origin.y) / view.scale,
    );
  }
}

export class LocalPoint {
  constructor(public x: number, public y: number) {}

  toClient(canvas: HTMLCanvasElement, view: PlaneView): ClientPoint {
    return this.toCanvas(canvas, view).toClient(canvas);
  }

  toCanvas(canvas: HTMLCanvasElement, view: PlaneView): CanvasPoint {
    const origin = CanvasPoint.origin(canvas, view);
    return new CanvasPoint(
      this.x * view.scale + origin.x,
      this.y * view.scale + origin.y,
    );
  }
}
