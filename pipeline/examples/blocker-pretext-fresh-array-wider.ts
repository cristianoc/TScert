// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): rich-inline.ts#materializeRichInlineLineRange.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim, the returned record's `fragments`.
// A local array of records with more fields, returned in a record whose
// field is an array of records with fewer: a mutable array is invariant in
// its element (a write through the wider view would break the narrower),
// and the model states no ownership by which a fresh array no other
// reference holds could be viewed at its wider element once returned.
type Fragment = { text: string };
type InternalFragment = Fragment & { start: number };
type Line = { fragments: Fragment[] };

export function materialize(texts: string[]): Line {
  const fragments: InternalFragment[] = [];
  for (let i = 0; i < texts.length; i++)
    fragments.push({ text: texts[i] ?? "", start: i });
  return { fragments };
}
