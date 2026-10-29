// `crypto.fips` through the default import of `node:crypto`: the
// declarations state `const fips: boolean`, but on the module's object Node
// holds a deprecated accessor answering 0, and no named export `fips` exists
// (run under Node: `typeof probe()` is "number"). A value of a Node module
// that no entry of the overlay reviews is refused where it is imported.
import crypto from "node:crypto";
export function probe(): boolean {
  return crypto.fips;
}
