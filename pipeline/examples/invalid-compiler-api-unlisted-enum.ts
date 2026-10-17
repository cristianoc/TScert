// `CharacterCodes` is no enum the compiler-API contract reads: its runtime
// object differs from its declaration (`ogham` is 5760 in the declaration
// and 5765 at run time), so a read of it is refused.
import { CharacterCodes } from "typescript/unstable/ast";

export function ogham(): number {
  return CharacterCodes.ogham;
}
