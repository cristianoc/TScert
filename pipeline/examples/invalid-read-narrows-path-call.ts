// A call between the test and the read, of a function that writes the
// tested member of a program record, which no stable link keeps; the type
// admits a present `undefined`. TypeScript keeps `d.initializer` narrowed
// across the call, and the call below returns `undefined` where a string is
// returned.

type Declaration = { kind?: string; initializer?: string | undefined };

function fail(reason: string): never {
  throw new Error(reason);
}

export function wrong(list: Declaration[], clear: () => void): string {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  clear();
  return d.initializer;
}
