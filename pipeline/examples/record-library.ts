// `Record<K, V>` is the standard library's mapped type `{ [P in K]: V }` at
// its arguments: string-literal keys are required fields, `string` a
// writable string index. A mapped type written in place reads the same way.
function point(): Record<"x" | "y", number> {
  return { x: 1, y: 2 };
}

function sumPoint(p: Record<"x" | "y", number>): number {
  return p.x + p.y;
}

function asFields(p: Record<"x" | "y", number>): { x: number; y: number } {
  return p;
}

function counts(): Record<string, number> {
  return { a: 1, b: 2 };
}

function asIndex(r: Record<string, boolean>): { [k: string]: boolean } {
  return r;
}

type Flags = { readonly [P in "on" | "off"]?: boolean };

function noFlags(): Flags {
  return {};
}

// Read inside a declaration's equation too.
type Scores = { best: Record<"math" | "art", number> };

function best(s: Scores): number {
  return s.best.art;
}

function total(): number {
  return sumPoint(point()) + best({ best: { math: 1, art: 2 } });
}
