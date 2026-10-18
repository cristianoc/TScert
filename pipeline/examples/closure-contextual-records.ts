// A closure parameter written without a type, inside its unit, is at the
// type TypeScript gives it from its context, which TScert reads: an
// anonymous record as its members state it, the same contract as the
// equivalent named one; a record an object literal's type gives; a mapped
// type's dictionary; a record of a generic declaration at its instance; a
// record at a binder; an enum member's literal.
interface Pair {
  a: number;
  readonly b?: string;
}

export function firsts(pairs: { a: number; readonly b?: string }[]): number[] {
  return pairs.map((o) => o.a);
}

export function firstsNamed(pairs: Pair[]): number[] {
  return pairs.map((o) => o.a);
}

export function joined(): string[] {
  const named = [{ cell: "a", name: "b" }];
  return named.map((n) => n.cell + n.name);
}

export function keys(rs: readonly Record<string, unknown>[]): unknown[] {
  return rs.map((r) => r["k"]);
}

interface Box<T> {
  readonly items: readonly { readonly v: T; w?: string }[];
}

export function inner(b: Box<number>): number[] {
  return b.items.map((i) => i.v);
}

export function values<T>(xs: readonly { v: T }[]): T[] {
  return xs.map((x) => x.v);
}

enum Kind {
  A = 1,
  B = 2,
}

const both: readonly (Kind.A | Kind.B)[] = [Kind.A, Kind.B];

export function isA(): boolean[] {
  return both.map((k) => k === Kind.A);
}

// An alias without parameters naming an interface's instance: the alias,
// with no arguments of its own.
interface Holder<T> {
  readonly held: T;
}
type NumberHolder = Holder<number>;

export function held(xs: readonly NumberHolder[]): number[] {
  return xs.map((x) => x.held);
}

// A mapped type's members: `Record`'s at the value it maps to; a mapped
// type over `keyof` written in the annotation at its value type and the
// modifiers it copies or overrides; a const literal's, readonly.
interface Point {
  readonly x: string;
  y?: string;
}

export function recorded(rs: readonly Record<"k", Point>[]): string[] {
  return rs.map((r) => r.k.x);
}

export function opened(
  ps: readonly { -readonly [K in keyof Point]-?: number }[],
): void {
  ps.forEach((p) => {
    p.x = p.y + 1;
  });
}

export function counted(
  cs: readonly { [K in keyof Point]: number }[],
): (number | undefined)[] {
  return cs.map((c) => c.y);
}

export function constant(): number[] {
  return [{ c: 1 } as const].map((o) => o.c);
}

// The records the forged controls (`pipeline/test.mts`) claim `firsts`'s
// closure at: its parameter's record without `a`, with `a` at `string`, with
// a field `c` added, with `b` required.
export function forgedAt(
  dropped: { readonly b?: string },
  narrowed: { a: string; readonly b?: string },
  added: { a: number; readonly b?: string; c: number },
  required: { a: number; readonly b: string },
): number {
  return [dropped, narrowed, added, required].length;
}
