// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getEmojiCorrection, measurement.ts#getPreparationLanguage,
// measurement.ts#readEmojiWidth.
// The DOM global `document`, tested by `typeof` and read at its root's
// `lang`, which the root has only where it is an HTML element.
export function language(): string | null {
  let language: string | null = null;
  if (typeof document !== "undefined") {
    const lang = (document.documentElement as HTMLElement | null | undefined)
      ?.lang;
    if (typeof lang === "string") language = lang;
  }
  return language;
}
