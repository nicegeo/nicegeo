import { VscodeButton } from "@vscode-elements/elements";

type ToolAction = () => void;

export class Tool {
  readonly id: string;
  private readonly label: string;
  private readonly icon: string;
  private readonly action: ToolAction;
  private button: VscodeButton | null = null;

  constructor(options: { id: string; label: string; icon: string; action: ToolAction }) {
    this.id = options.id;
    this.label = options.label;
    this.icon = options.icon;
    this.action = options.action;
  }

  render(onSelect: (tool: Tool) => void): VscodeButton {
    const button = document.createElement("vscode-button") as VscodeButton;
    button.id = `toolButton-${this.id}`;
    button.className = "toolButton";
    button.title = this.label;
    button.icon = this.icon;

    button.addEventListener("click", () => {
      onSelect(this);
      this.action();
    });

    this.button = button;
    return button;
  }

  setActive(isActive: boolean): void {
    if (!this.button) return;
    this.button.classList.toggle("toolButtonActive", isActive);
  }
}

export class Section {
  private readonly title: string;
  private readonly className: string;
  private readonly tools: Tool[];
  private readonly isModifier: boolean;
  private activeTool: Tool | null;

  constructor(options: {
    title: string;
    className: string;
    tools: Tool[];
    isModifier?: boolean;
    activeTool?: Tool;
  }) {
    this.title = options.title;
    this.className = options.className;
    this.tools = options.tools;
    this.isModifier = options.isModifier ?? false;
    this.activeTool = options.activeTool ?? null;
  }

  render(): HTMLElement {
    const section = document.createElement("section");
    section.className = this.className;

    const titleElement = document.createElement("span");
    titleElement.className = "sectionTitle";
    titleElement.textContent = this.title;

    const group = document.createElement("div");
    group.className = "group";
    group.append(...this.tools.map((tool) => tool.render(this.onToolSelected)));

    section.append(titleElement, group);
    this.updateActiveToolButtons();
    return section;
  }

  private readonly onToolSelected = (tool: Tool): void => {
    if (this.isModifier) return;
    this.activeTool = tool;
    this.updateActiveToolButtons();
  };

  private updateActiveToolButtons(): void {
    if (this.isModifier) return;

    for (const tool of this.tools) {
      tool.setActive(tool === this.activeTool);
    }
  }
}
