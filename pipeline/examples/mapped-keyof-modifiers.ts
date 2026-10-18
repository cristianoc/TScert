// A mapped type over `keyof` copies its source's modifiers where it writes
// none, and applies those it writes: `a` stays readonly and `b` optional,
// `-readonly` makes `a` writable, `-?` makes `b` required.
interface Source {
  readonly a: string;
  b?: string;
}

type Counts = { [K in keyof Source]: number };
type Open = { -readonly [K in keyof Source]: number };
type Full = { [K in keyof Source]-?: boolean };

export function count(c: Counts, o: Open, f: Full): number {
  o.a = c.a;
  return f.b ? c.a : (c.b ?? 0);
}
