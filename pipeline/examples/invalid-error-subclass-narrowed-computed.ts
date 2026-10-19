// The same narrowing at a computed key: refused at the receiver's declared
// type (run under Node).
class Decline extends Error {
  readonly kind: "error" = "error";
}
type Entry = { kind: "record"; name: number; stack?: string };
type Box = { v: Entry | Decline };

export function traced(
  box: Box,
  change: (b: Box) => void,
  k: "stack",
): string[] {
  if (box.v.kind === "record") {
    change(box);
    box.v[k] = "s";
  }
  return Object.keys(box.v);
}
