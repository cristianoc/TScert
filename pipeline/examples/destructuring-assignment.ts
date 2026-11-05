// An object destructuring assignment to existing bindings, as a
// statement: the right side once, then each property's read, its default
// where the read is `undefined`, and its target's write, in source order.

type Pair = { a: number; b?: number };

// The right side runs once; a later default reads an earlier target.
export function once(make: () => Pair): number {
  let a = 0;
  let b = 0;
  ({ a, b = a } = make());
  return a * 10 + b;
}

// A default applies to `undefined` only, not to `null`.
export function nullKept(o: { v?: string | null }): string {
  let v: string | null = "init";
  ({ v = "default" } = o);
  return v === null ? "null" : v;
}

// Renamed and nested targets.
export function nested(o: { p: { x: number; y: number }; q: string }): string {
  let x = 0;
  let y = 0;
  let label = "";
  ({ p: { x, y }, q: label } = o);
  return `${label}${x + y}`;
}

// A target a closure captures: the closure reads the written value.
export function captured(o: { n: number }): number {
  let n = 1;
  const read = (): number => n;
  ({ n } = o);
  return read();
}

// A block's binding of the same name is another binding.
export function shadowed(o: { s: string }): string {
  let s = "outer";
  {
    let s = "inner";
    ({ s } = o);
    if (s.length > 100) return s;
  }
  return s;
}
