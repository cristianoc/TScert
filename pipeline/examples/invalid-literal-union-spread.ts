// The literal names the `square` kind, so it is built at that arm, but
// without the spread it lacks `side`: the copy is either record, and the one
// with no `side` meets no arm.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
export function bad(wide: boolean): Shape {
  return { kind: "square", ...(wide ? { side: 2 } : {}) };
}
