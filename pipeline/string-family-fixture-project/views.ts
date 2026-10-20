// Read by pipeline/test.mts on the stand-in string-tagged family: its
// `Program` interface and `API` class share names with the compiler API's
// named views, which apply to the compiler API's installation alone, so
// their members are read as the stand-in declares them.
import type { API, Program } from "string-family-fixture/ast";

export function extra(p: Program): number {
  return p.extra;
}

export function apiName(a: API): string {
  return a.name;
}
