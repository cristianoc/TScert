// The false edge of a truthiness test keeps the falsy strings: past
// `if (d.initializer) return undefined;` the member is `""` or absent, so
// `wrong([{ initializer: "" }])` returns `""` where `undefined` is returned
// (TypeScript also refuses it, TS2322).

type Declaration = { kind?: string; initializer?: string };

function fail(reason: string): never {
  throw new Error(reason);
}

export function wrong(list: readonly Declaration[]): undefined {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (d.initializer) return undefined;
  return d.initializer;
}
