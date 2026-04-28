import type { Tool } from "./tools";

abstract class Section {
  private readonly title: string;
  private readonly className: string;
  protected readonly items: Tool[];

  constructor(options: {
    title: string;
    className: string;
    items: Array<new (onSelect: (tool: Tool) => void) => Tool>;
  }) {
    this.title = options.title;
    this.className = options.className;
    this.items = options.items.map(cls => new cls(tool => this.onItemSelected(tool)));
  }

  render(): HTMLElement {
    const section = document.createElement("section");
    section.className = this.className;

    const titleElement = document.createElement("span");
    titleElement.className = "sectionTitle";
    titleElement.textContent = this.title;

    const group = document.createElement("div");
    group.className = "group";
    group.append(...this.items.map(item => item.render()));

    section.append(titleElement, group);
    return section;
  }

  protected abstract onItemSelected(item: Tool): void;
}

export class ToolSection extends Section {
  private activeTool: Tool | null = null;

  protected override onItemSelected = (tool: Tool): void => {
    if (this.activeTool) {
      this.activeTool.enabled = false;
    }

    this.activeTool = this.activeTool === tool ? null : tool;

    if (this.activeTool) {
      this.activeTool.enabled = true;
    }
  };
}

export class ModifierSection extends Section {
  private readonly activeModifiers: Set<Tool> = new Set();

  protected override onItemSelected = (modifier: Tool): void => {
    if (this.activeModifiers.has(modifier)) {
      this.activeModifiers.delete(modifier);
      modifier.enabled = false;
    } else {
      this.activeModifiers.add(modifier);
      modifier.enabled = true;
    }
  };
}