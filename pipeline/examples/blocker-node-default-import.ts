// An export-assigned Node module default import needs its merged declarations
// resolved.
// Census functions:
// shadow-contracts.mts#shadowText.
import path from "node:path";
export function use(s: string): string {
  return path.basename(s);
}
