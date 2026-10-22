// A write of the tested member through another reference to the same
// object, between the test and the read: TypeScript keeps `d.initializer`
// narrowed, and `wrong([{ initializer: "a" }])` returns `undefined` where a
// string is returned.

type Declaration = { kind?: string; initializer: string | undefined };

function fail(reason: string): never {
  throw new Error(reason);
}

export function wrong(list: Declaration[]): string {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  list[0].initializer = undefined;
  return d.initializer;
}
