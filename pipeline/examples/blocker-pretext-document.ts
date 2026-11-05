// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getEmojiCorrection, measurement.ts#getPreparationLanguage,
// measurement.ts#readEmojiWidth.
// Refusal: gate: the global document is declared in
// typescript/lib/lib.dom.d.ts (library), an origin no reviewed entry
// admits.
// The DOM global `document`, which has no reviewed entry.
export function language(): string {
  return typeof document === "undefined" ? "" : document.documentElement.lang;
}
