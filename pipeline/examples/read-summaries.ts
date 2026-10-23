// Reads of a slot holding a union: a readonly view each member states is
// read through one checked summary of the request (`readSummary`), a view
// of `length` at a type excluding a number included; a writable field, an
// optional field, a dictionary's index, a callable object's field, a class
// value's readonly static field, a receiver coerced to its base, an array's or a string's `length` and a
// primitive's member read through its wrapper's prototype keep their own
// rules. The read-summary controls of pipeline/test.mts forge summaries
// beside these reads.
type A = {
  readonly k: "a";
  readonly t: 1;
  readonly length: number;
  w: number;
  o?: number;
};
type B = {
  readonly k: "b";
  readonly t: 2;
  readonly length: number;
  w: number;
  o?: number;
};
type D = { readonly k: "d"; readonly [key: string]: string };
type E = { readonly k: "e"; readonly [key: string]: string };
type L = { readonly length: "l" };
type M = { readonly length: "m" };
type F = { (): number; tag: "f" };
type G = { (): number; tag: "g" };
class P {
  static readonly tag = "p";
}
class Q {
  static readonly tag = "q";
}

export function kindOf(x: A | B): "a" | "b" {
  return x.k;
}

export function kindTwice(x: A | B): string {
  const first = x.k;
  const second = x.k;
  return first === second ? first : second;
}

export function tagOf(x: A | B): 1 | 2 {
  return x.t;
}

export function entryKind(x: D | A): string {
  return x.k;
}

export function lengthView(x: L | M): "l" | "m" {
  return x.length;
}

export async function kindAwaiting<T>(value: T, x: A | B): Promise<Awaited<T>> {
  const kind = x.k;
  if (kind === "a") return await value;
  return await value;
}

export function kindOfCell(y: A | B, z: A | B): () => "a" | "b" {
  let x = y;
  const read = (): "a" | "b" => x.k;
  x = z;
  return read;
}

export function widthOf(x: A | B): number {
  return x.w;
}

export function optionalOf(x: A | B): number | undefined {
  return x.o;
}

export function indexOf(x: D | E): string | undefined {
  return x.other;
}

export function tagOfCallable(x: F | G): "f" | "g" {
  return x.tag;
}

export function classTag(x: typeof P | typeof Q): "p" | "q" {
  return x.tag;
}

export function errorName(e: TypeError | RangeError): string {
  return e.name;
}

export function sizeOf(x: readonly string[] | readonly number[]): number {
  return x.length;
}

export function textSize(x: string | readonly string[]): number {
  return x.length;
}

export function upper(x: "a" | "b"): string {
  return x.toUpperCase();
}
