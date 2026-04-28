import { VscodeButton } from "@vscode-elements/elements";
import { Construction, Point } from "./constructions";

export interface ConstructionInput { kind: "construction"; construction: Construction }
export interface LocationInput { kind: "location"; x: number; y: number }
export type ToolInput = ConstructionInput | LocationInput;

export interface ConstructionResult { kind: "construction"; construction: Construction }
export interface FailureResult { kind: "failure" }
export interface ContinueResult { kind: "continue" }
export type ToolResult = ConstructionResult | FailureResult | ContinueResult;

export abstract class Tool {
  readonly id: string;

  private readonly label: string;
  private readonly icon: string;

  private _enabled = false;
  private button: VscodeButton | null = null;

  constructor({id, label, icon}: { id: string; label: string; icon: string }) {
    this.id = id;
    this.label = label;
    this.icon = icon;
  }

  get enabled(): boolean {
    return this._enabled;
  }

  set enabled(isEnabled: boolean) {
    this._enabled = isEnabled;
    if (!this.button) return;
    this.button.classList.toggle("toolButtonActive", isEnabled);
  }

  abstract activate(input: ToolInput): ToolResult;

  abstract reset(): void;

  abstract get inputs(): readonly Construction[];

  render(onSelect: (tool: Tool) => void): VscodeButton {
    const button = document.createElement("vscode-button") as VscodeButton;
    button.id = `toolButton-${this.id}`;
    button.className = "toolButton";
    button.title = this.label;
    button.icon = this.icon;

    button.addEventListener("click", () => {
      onSelect(this);
    });

    this.button = button;
    return button;
  }
}

export class PointTool extends Tool {
  constructor() {
    super({
      id: "point",
      label: "Point",
      icon: "circle-filled",
    });
  }

  override activate(input: ToolInput): ToolResult {
    if (input.kind !== "location") return { kind: 'failure' };
    const { x, y } = input;
    const p = new Point('', x, y);
    return { kind: 'construction', construction: p };
  }

  override get inputs(): readonly Construction[] {
    return [];
  }

  override reset(): void {}
}

export class LineTool extends Tool {
  private readonly points: Point[] = [];

  constructor() {
    super({
      id: "line",
      label: "Line",
      icon: "arrow-both",
    });
  }

  override activate(input: ToolInput): ToolResult {
    return { kind: 'failure' };
  }

  override reset(): void {
    this.points.length = 0;
  }

  override get inputs(): readonly Construction[] {
    return this.points;
  }
}

export class CircleTool extends Tool {
  private readonly points: Point[] = [];

  constructor() {
    super({
      id: "circle",
      label: "Circle",
      icon: "circle-large",
    });
  }

  override activate(input: ToolInput): ToolResult {
    return { "kind": "failure" };
  }

  override reset(): void {
    this.points.length = 0;
  }

  override get inputs(): readonly Construction[] {
    return this.points;
  }
}

export class DistinctModifier extends Tool {
  private readonly points: Point[] = [];

  constructor() {
    super({
      id: "distinct",
      label: "Distinct",
      icon: "diff-removed",
    });
  }

  override activate(input: ToolInput): ToolResult {
    return { "kind": "failure" };
  }

  override reset(): void {
    this.points.length = 0;
  }

  override get inputs(): readonly Construction[] {
    return this.points;
  }
}
