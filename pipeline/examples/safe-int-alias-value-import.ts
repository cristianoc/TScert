// An alias of the verifier's `SafeInt` is `SafeInt`: recognition follows
// the declaration TypeScript binds the name to, here through a local alias
// and an exported one of another module.
import type { Count } from "@fixture/safe-int-count";

type Index = SafeInt;

function keep(i: SafeInt): SafeInt {
  return i;
}

export function viaLocal(i: Index): SafeInt {
  return keep(i);
}

export function viaImport(i: Count): SafeInt {
  return keep(i);
}
