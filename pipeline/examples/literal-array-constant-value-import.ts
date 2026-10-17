// An imported constant initialized by an array literal is admitted by the
// table of types stated by annotations, and the declaration reader does not
// read it yet: refused where it is imported.
import { offsets } from "@fixture/lib";

export function first(): number {
  return offsets.length;
}
