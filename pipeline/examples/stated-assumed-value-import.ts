// An imported function whose statement its own module's run refuses (it
// pops the array it is handed): the importer reads it at its declaration,
// the statement included, which is the import assumption, so the callback
// is within the empty footprint and the importer verifies relative to it.
// That the linked program meets every statement needs each module's run to
// pass: `drain`'s does not.
import { drain } from "@fixture/stated";

export function drained(xs: number[]): number[] {
  const r: number[] = xs.map((x) => drain(xs, x));
  return r;
}
