// The namespace object itself is a value no named import stands for: a read
// of it other than a member read is refused.
import * as lib from "@fixture/lib";

export function whole(): number {
  const m = lib;
  return m.limit;
}
