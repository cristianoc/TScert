// A completed member read narrows its receiver: reading a member of `null`
// or `undefined` throws, so past `d.kind` the constant `d` holds an object.

type Declaration = { kind?: string; initializer?: string };

function fail(reason: string): never {
  throw new Error(reason);
}

function describe(d: Declaration): string {
  return d.initializer ?? "none";
}

// The reads of a later statement, and its tests, are of the object.
export function initializer(list: readonly Declaration[]): string {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  return d.initializer;
}

// The object is passed where only an object is accepted.
export function described(list: readonly Declaration[]): string {
  const d = list[0];
  const k = d.kind;
  return describe(d) + (k ?? "");
}

// An owned local is narrowed by the read too, until it is written.
export function owned(list: readonly Declaration[], other: Declaration): string {
  let d = list[0];
  const k = d.kind ?? "";
  const first = describe(d);
  d = other;
  return k + first + describe(d);
}
