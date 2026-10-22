// A call evaluated between the test and the read, as an earlier actual of
// the call the read is an actual of: it writes the tested member, which the
// type admits `undefined` at, and the call below returns `undefined` where a
// string is returned. TypeScript keeps `d.initializer` narrowed.

type Declaration = { kind?: string; initializer?: string | undefined };

function fail(reason: string): never {
  throw new Error(reason);
}

function second(first: number, text: string): string {
  return first > 0 ? text : text;
}

export function wrong(list: Declaration[], clear: () => number): string {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  return second(clear(), d.initializer);
}
