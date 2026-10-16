// A static block is code the class definition runs, where it stands among
// the static fields: `static { S }` is `(() => { S })()`, its declarations
// its own. It reads the class's statics by name, never through `this`.
declare function register(name: string, size: number): void;

class Registry {
  static readonly name0: string = "registry";
  static readonly size: number = 3;
  static {
    const doubled = Registry.size * 2;
    let label = Registry.name0;
    if (doubled > 4) label = label + "!";
    register(label, doubled);
  }
  static readonly after: number = Registry.size + 1;
}

export function use(): number {
  return Registry.after;
}
