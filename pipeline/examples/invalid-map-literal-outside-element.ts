// A `map` callback returning a field literal the element type does not name:
// the expected result fixes `map`'s `U`, and `"space"` is no `Token` kind.
type Token = { kind: "code" | "word"; text: string };

export function tokens(xs: string[]): Token[] {
  // @ts-expect-error: "space" is not a Token kind
  return xs.map((t) => ({ kind: t === " " ? "space" : "word", text: t }));
}
