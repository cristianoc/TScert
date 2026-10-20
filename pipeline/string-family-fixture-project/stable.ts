// The stand-in family's stable members (HOST-FAMILIES.md, "Stable keys"):
// a call's callee tested and read past an unrelated call. Under the
// stand-in's description every property member is stable; one excluding
// `Call.callee` makes the same program refused at the read.
import { isName, type Call } from "string-family-fixture/ast";

export function calleeName(c: Call, log: () => void): string {
  if (!isName(c.callee)) return "";
  log();
  return c.callee.name;
}
