// A bounded binder admits no instance outside its bound: numbers are not
// Booleans, whatever the call's arguments are.
import { flags } from "@fixture/lib";
export function outside(n: number): number {
  return flags.either(n, n);
}
