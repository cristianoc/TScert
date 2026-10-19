// A named import of `node:assert/strict`'s `ifError` would be read at its
// declaration, whose promise only it asserts: refused, the module read
// through its default import alone.
import { ifError } from "node:assert/strict";

export function cleared(e: string | null | undefined): null | undefined {
  ifError(e);
  return e;
}
