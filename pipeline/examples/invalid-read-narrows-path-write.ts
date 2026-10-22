// A write of the root between the path's test and its read: the read is of
// the written declaration, which the test did not see, so
// `wrong([{ initializer: "a" }], {})` returns `undefined` where a string is
// returned (TypeScript also refuses it, TS2322).

type Declaration = { kind?: string; initializer?: string };

function fail(reason: string): never {
  throw new Error(reason);
}

export function wrong(
  list: readonly Declaration[],
  other: Declaration,
): string {
  let d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  d = other;
  return d.initializer;
}
