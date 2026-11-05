// pretext: getBlinkDefaultLocale.
export function locale(): string {
  return new Intl.DateTimeFormat().resolvedOptions().locale
}
