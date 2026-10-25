// A contextual reference to a generic alias needs its omitted default argument
// completed.
// Census functions:
// diagnostic-view.mts#presentObligation.
import type { ObligationDiagnostic } from "../../tools/diagnostic.mts";
export function use(ob: ObligationDiagnostic): number {
  if (ob.kind !== "edge-coverage") return 0;
  const required = ob.destination.claim?.context ?? [];
  return required.findIndex((need) => need.length === 0);
}
