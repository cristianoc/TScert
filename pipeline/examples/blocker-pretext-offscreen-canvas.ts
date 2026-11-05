// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#createContext.
// Refusal: gate: the global OffscreenCanvas is declared in
// typescript/lib/lib.dom.d.ts (library), an origin no reviewed entry
// admits.
// The DOM global `OffscreenCanvas`, which has no reviewed entry.
export function hasCanvas(): boolean {
  if (typeof OffscreenCanvas !== "undefined")
    return new OffscreenCanvas(1, 1).getContext("2d") !== null;
  return false;
}
