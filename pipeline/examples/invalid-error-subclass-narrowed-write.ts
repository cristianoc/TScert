// TypeScript narrows `box.v` to the record at the test and keeps it after
// `change`, which may have put an instance there: the write of `stack` then
// reaches the instance, whose own `stack` stays non-enumerable (run under
// Node). The receiver is judged at its declared type, refused.
class Decline extends Error {
  readonly kind: "error" = "error";
}
type Entry = { kind: "record"; name: number; stack?: string };
type Box = { v: Entry | Decline };

export function traced(box: Box, change: (b: Box) => void): string[] {
  if (box.v.kind === "record") {
    change(box);
    box.v.stack = "s";
  }
  return Object.keys(box.v);
}
