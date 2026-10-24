// A function stating {value: any, store: grow} that serializes a record
// with `JSON.stringify` and a replacer: a value of the record's type may
// hold a `toJSON`, or a getter in a field the type does not state, which
// serializing calls and which may remove an element of an array. A record
// is no JSON value, so the call is refused at the stated parameter, and the
// statement is not established.
type Term = { k: string; span: number };

function sameTerm(
  a: Term,
  b: Term,
): Within<{ value: "any"; store: "grow" }, boolean> {
  const text = (t: Term): string =>
    JSON.stringify(t, (key, value: unknown) =>
      key === "span" ? undefined : value,
    ) ?? "";
  return text(a) === text(b);
}

export function wrong(xs: number[], t: Term): number[] {
  return xs.map((x) => (sameTerm(t, t) ? x : 0));
}
