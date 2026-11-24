// Imported identity-shaped functions (`return p`, `const y = p; return y`, and
// multi-return branches) publish their pass-inferred return-alias postconditions
// in the module interface, so facts learned on each returned alias transfer back
// to the caller's argument.
import {
  branchId,
  directId,
  localId,
  type Pair,
} from "@fixture/identity-return";

export function firstViaDirect(p: Pair): number {
  const alias = directId(p);
  if (alias.flags.length === 0) return 0;
  return p.widths[0]!;
}

export function firstViaLocal(p: Pair): number {
  const alias = localId(p);
  if (alias.flags.length === 0) return 0;
  return p.widths[0]!;
}

export function firstViaBranch(p: Pair, flag: boolean): number {
  const alias = branchId(p, flag);
  if (alias.flags.length === 0) return 0;
  return p.widths[0]!;
}
