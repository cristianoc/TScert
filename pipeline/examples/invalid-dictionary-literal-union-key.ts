// A dictionary read at a key that may be any string or one literal,
// `string | ""` as a `let` holds it after a write of `""`: the key is any
// string, so the read may find a member every object inherits from
// `Object.prototype` (`constructor` at the key "constructor"), a function
// where the dictionary's type says an array or nothing. Pretext's
// line-breaks.ts#getWebKitLineRules reads its quote remaps so
// (blocker-pretext-widened-key-read).
const remaps: Record<string, readonly number[]> = { "": [0], ab: [1] };

export function remapOf(locale: string): readonly number[] {
  let name = locale;
  let remap = remaps[name];
  while (remap === undefined) {
    const cut = name.lastIndexOf("_");
    name = cut < 0 ? "" : name.slice(0, cut);
    remap = remaps[name];
  }
  return remap;
}
