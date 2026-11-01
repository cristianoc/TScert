// Census functions:
// host-families.mts#footprintReading
// library-modules.mts#moduleEntries
// library-modules.mts#moduleObjectDefault
import type { CallEffect } from "../../tools/declaration-types.mts";
import { emptyEffect } from "../../tools/type-graph.mts";
export function effect(): CallEffect {
  return {
    footprint: emptyEffect.footprint,
    promise: emptyEffect.promise,
    fresh: emptyEffect.fresh,
    receiverStore: emptyEffect.receiverStore,
    onThrow: true,
    receiverOwn: emptyEffect.receiverOwn,
    freshObject: emptyEffect.freshObject,
    requires: emptyEffect.requires,
    elements: emptyEffect.elements,
  };
}
