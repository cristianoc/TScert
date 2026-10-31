// A finite-key record leaves other own values unconstrained.
// Object.values cannot supply the array parameter of this callback.
// Census functions:
// array-prototype.mts#primitivePrototype
// array-prototype.mts#functionPrototype
// array-prototype.mts#reviewedEntries
// array-prototype.mts#mergeRefusal
// array-prototype.mts#prototype
import type { OverlayEntry } from "../../tools/array-prototype.mts";
export function entries(
  name: string,
  overlay: readonly OverlayEntry[],
  primitive: Readonly<
    Record<"string" | "number" | "boolean", readonly OverlayEntry[]>
  >,
  interfaces: Map<string, readonly OverlayEntry[]>,
): OverlayEntry[] {
  const from = name === "Array" ? ["Array", "ReadonlyArray"] : [name];
  return [overlay, ...Object.values(primitive), ...interfaces.values()].flatMap(
    (entries) => entries.filter((entry) => from.includes(entry.from)),
  );
}
