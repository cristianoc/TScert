// A function stating {value: any, store: grow} that serializes a record
// with `JSON.stringify` and a replacer: a value of the record's type may
// hold a `toJSON`, which serializing calls and which may remove an element
// of an array. A record is no JSON value, so the call is refused at its
// argument, before the function's statement is checked.
type Term = { k: string; span: number };

function sameTerm(
  a: Term,
  b: Term,
): Modifies<{ values: "any"; stores: "grow" }, boolean> {
  const text = (t: Term): string =>
    JSON.stringify(t, (key, value: unknown) =>
      key === "span" ? undefined : value,
    ) ?? "";
  return text(a) === text(b);
}

export function wrong(xs: number[], t: Term): number[] {
  return xs.map((x) => (sameTerm(t, t) ? x : 0));
}
