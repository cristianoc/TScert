// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): line-breaks.ts#getBlinkDefaultLocale.
// Refusal: gate: TypeScript resolves new Intl.DateTimeFormat(…) to no
// construct signature of a constant Intl declares.
// The default locale read as `new Intl.DateTimeFormat().resolvedOptions()
// .locale`: the namespace's reviewed entries state `Intl.Segmenter`'s
// construction alone.
let defaultLocale: string | null = null;

export function getDefaultLocale(): string {
  return (defaultLocale ??= new Intl.DateTimeFormat().resolvedOptions().locale);
}
