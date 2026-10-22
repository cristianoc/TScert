// A template literal converts an object operand by the object's own
// `toString`, code a record's type does not state: here one that clears
// `b.v` after the test. The conversion is refused. Under Node,
// `bad({ v: 1, toString() { box.v = undefined; return ""; } }, box)` with
// `box = { v: "s" }` returns `undefined`.
interface Box {
  v: string | undefined;
}

export function bad(x: { readonly v: number }, b: Box): string {
  if (b.v === undefined) return "";
  const s = `${x}`;
  return s.length === 0 ? b.v : s;
}
