// `Object.freeze` of a fresh object literal of named fields is
// `%Freeze:K%`: the result, the only reference to the frozen object, holds
// the fields as readonly views, so no write reaches it. An object a field
// holds is not frozen, and stays writable. The ReScript runtime's
// nested-option markers, cached in a `Map`.
type Marker = { readonly BS_PRIVATE_NESTED_SOME_NONE: number };

const markers: Map<number, Marker> = new Map();

export function marker(depth: number): Marker {
  const m = markers.get(depth);
  if (m !== undefined) {
    return m;
  }
  const fresh = Object.freeze({ BS_PRIVATE_NESTED_SOME_NONE: depth });
  markers.set(depth, fresh);
  return fresh;
}

export function depthOf(depth: number): number {
  const m = Object.freeze({
    BS_PRIVATE_NESTED_SOME_NONE: depth,
    kind: "marker",
  });
  return m.BS_PRIVATE_NESTED_SOME_NONE;
}

export function nested(a: number): number {
  const f = Object.freeze({ inner: { a } });
  f.inner.a = a + 1;
  return f.inner.a;
}
