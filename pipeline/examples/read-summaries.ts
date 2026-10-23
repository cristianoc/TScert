// Reads of a slot holding a union: a readonly view each member states is
// read through one checked summary of the request (`readSummary`); a
// writable field, a `length` view at a number, an optional field, a
// dictionary's index and a key read through the prototype keep their own
// rules. The read-summary controls of pipeline/test.mts forge summaries
// beside these reads.
type A = { readonly k: "a"; readonly length: number; w: number; o?: number };
type B = { readonly k: "b"; readonly length: number; w: number; o?: number };
type D = { readonly k: "d"; readonly [key: string]: string };

export function kindOf(x: A | B): "a" | "b" {
  return x.k;
}

export function kindTwice(x: A | B): string {
  const first = x.k;
  const second = x.k;
  return first === second ? first : second;
}

export function entryKind(x: D | A): string {
  return x.k;
}

export function widthOf(x: A | B): number {
  return x.w;
}

export function optionalOf(x: A | B): number | undefined {
  return x.o;
}

export function errorName(e: TypeError | RangeError): string {
  return e.name;
}

export function kindOfCell(y: A | B, z: A | B): () => "a" | "b" {
  let x = y;
  const read = (): "a" | "b" => x.k;
  x = z;
  return read;
}
