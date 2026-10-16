// A source symbol spelled as the native mark is a key of its own: the mark's
// symbol is synthetic, declared by no source, so this value, which states
// every member `matchAll` dispatches to, is no native regex, and `matchAll`
// of it is refused.
declare const RegExpMatcher: unique symbol;
type Forged = RegExp & {
  readonly [RegExpMatcher]: undefined;
  [Symbol.matchAll](s: string): Iterator<RegExpExecArray>;
};

export function matches(re: Forged, s: string): boolean {
  const all = s.matchAll(re);
  return s.length > 0;
}
