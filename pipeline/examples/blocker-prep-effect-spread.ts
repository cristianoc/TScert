// Census functions:
// host-families.mts#footprintReading
// library-modules.mts#moduleEntries
// library-modules.mts#moduleObjectDefault
import type { CallEffect } from "../../tools/declaration-types.mts";
import { emptyEffect } from "../../tools/type-graph.mts";
export function effect(): CallEffect {
  return { ...emptyEffect, onThrow: true };
}
