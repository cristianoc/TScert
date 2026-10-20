// A member of a host view, the sync API's `Signature`, tested and read past
// a call: no family states a view's members stable, so the test's fact
// ends at the call and the read is of the declared type (HOST-FAMILIES.md,
// "Stable links").
import type { Signature } from "typescript/unstable/sync";

export function thisParameter(s: Signature, log: () => void): number {
  if (s.thisParameter === undefined) return 0;
  log();
  return s.thisParameter;
}
