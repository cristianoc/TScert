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

// A mapped type's members at its instance: `Record`'s at the value it maps
// to; an alias over `keyof` writing both modifiers, each member writable and
// required; a const literal's, readonly.
interface Point {
  readonly x: number;
  y?: number;
}

export function recorded(rs: readonly Record<"k", Point>[]): number[] {
  return rs.map((r) => r.k.x);
}

type Open = { -readonly [K in keyof Point]-?: number };

export function opened(ps: readonly Open[]): void {
  ps.forEach((p) => {
    p.x = p.y;
  });
}

export function constant(): number[] {
  return [{ c: 1 } as const].map((o) => o.c);
}
