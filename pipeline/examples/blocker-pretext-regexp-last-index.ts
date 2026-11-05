// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): han-kerning.ts#getStaticCharType.
// Refusal: reject: source refusal: a write of 'lastIndex', a key the
// object's type does not state.
// A sticky regular expression positioned by a write of its `lastIndex`,
// then tested: the model's regular expressions state their methods alone
// (SOURCE-FRAGMENT.md, a regex's property), so the write is refused. The
// test of the one code point at the index needs no position:
// `/^\p{Ps}$/u.test(String.fromCodePoint(cp))`.
const openPunctuationRe = /\p{Ps}/uy;

export function opensAt(text: string, index: number): boolean {
  openPunctuationRe.lastIndex = index;
  return openPunctuationRe.test(text);
}
