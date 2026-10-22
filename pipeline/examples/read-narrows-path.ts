// A member path rooted at a receiver a completed read narrowed: past
// `d.kind` the constant `d` read from an element holds an object, and a
// test of `d.initializer` refines the read of the path in the statements
// it guards, after a call that never returns, as `patternStmt` reads a
// declaration's initializer (run under Node).

type Declaration = { readonly kind?: string; readonly initializer?: string };

function fail(reason: string): never {
  throw new Error(reason);
}

function width(text: string): number {
  return text.length;
}

export function initializerWidth(list: readonly Declaration[]): number {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  return width(d.initializer);
}

class Measure {
  width(text: string): number {
    return text.length;
  }
}

// Evaluating the callee `m.width` reads a method and allocates its bound
// function, which keeps every read link.
export function measured(m: Measure, list: readonly Declaration[]): number {
  const d = list[0];
  if (d.kind) fail("an annotated declaration");
  if (!d.initializer) fail("a declaration needs an initializer");
  return m.width(d.initializer);
}

export function guarded(list: readonly Declaration[]): number {
  const d = list[0];
  if (d.initializer) return width(d.initializer);
  return 0;
}

export function returned(list: readonly Declaration[]): number {
  const d = list[0];
  const annotated = d.kind ? 1 : 0;
  if (!d.initializer) return -1;
  return width(d.initializer) + annotated;
}
