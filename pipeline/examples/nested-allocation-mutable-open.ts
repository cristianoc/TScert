// Nested object literals whose enclosing field is reassigned or passed to a
// mutable open-field contract are allocated open so invariance holds.
function takeMutable(b: { inner: { a: number } }): number {
  return b.inner.a;
}

function id<T>(x: T): T {
  return x;
}

export function reassignNestedField(openRec: { a: number }): number {
  const box = { inner: { a: 1 } };
  box.inner = openRec;
  return box.inner.a;
}

export function passToMutableParam(): number {
  const box = { inner: { a: 1 }, tag: "ok" };
  const n = takeMutable(box);
  return n + box.tag.length;
}

export function returnMutableBox(): { inner: { a: number } } {
  const box = { inner: { a: 1 } };
  return box;
}

export function reassignDeepAndAlias(openRec: { a: number }): number {
  const deep = { outer: { inner: { a: 1 } } };
  deep.outer.inner = openRec;
  const box = { inner: { a: 2 } };
  const alias = box;
  alias.inner = openRec;
  return deep.outer.inner.a + box.inner.a;
}

export function genericIdReturn(): { inner: { a: number } } {
  return id({ inner: { a: 1 } });
}

type Overloaded = ((
  service: { readonly build: (x: number) => { readonly a: number } },
  opts: { leader: { host: string }; lazies?: { a?: () => number } },
) => number) &
  ((
    service: {
      readonly build: (x: number) => { readonly a: number; readonly b: string };
    },
    opts: {
      leader: { host: string };
      lazies?: { a?: () => number; b?: () => string };
    },
  ) => number);

export function overloadedNestedLiteralFallback(f: Overloaded): number {
  return f(
    { build: (x) => ({ a: x, b: "ok" }) },
    { leader: { host: "localhost" }, lazies: { b: () => "hi" } },
  );
}
