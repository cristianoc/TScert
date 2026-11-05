// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getWebKitGenericFamilies, line-breaks.ts#getWebKitLineRules.
// Refusal: search: a read at a key that may name a member every object
// inherits from `Object.prototype`.
// A dictionary read at a `let` key a literal write widened, `string |
// "zh-hans"` as TypeScript's flow types it, then shortened in a loop until
// the dictionary holds it: the key is any string, so `families[tag]` may
// find a member of `Object.prototype` (`toString` at the key "toString").
export const families: Readonly<Record<string, readonly number[]>> = {
  "": [0, 1],
};
export function row(language: string, han: boolean): readonly number[] {
  let tag = language.toLowerCase();
  if (han) tag = "zh-hans";
  let found = families[tag];
  while (found === undefined) {
    tag = tag.slice(0, Math.max(0, tag.lastIndexOf("-")));
    found = families[tag];
  }
  return found;
}
