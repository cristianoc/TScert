// An open read grants no write: no type states the key, so a write at it
// has no contract to keep.
export function mark(x: unknown): void {
  if (typeof x === "object" && x !== null && "seen" in x) x.seen = true;
}
