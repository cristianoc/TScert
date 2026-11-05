// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#buildEngineProfile.
// Refusal: gate: the global navigator is declared in
// typescript/lib/lib.dom.d.ts (library), an origin no reviewed entry
// admits.
// The DOM global `navigator`, which has no reviewed entry.
export function agent(): string {
  return typeof navigator === "undefined" ? "" : navigator.userAgent;
}
