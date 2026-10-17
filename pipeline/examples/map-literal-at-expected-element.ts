// A `map` callback returning an object literal whose field is a conditional
// of string literals, at a return type naming the literals: the call's
// expected result fixes `map`'s `U`, so the literal is typed at the element
// type, as TypeScript infers from the return position first.
type Token = { kind: "code" | "word"; text: string };

export function tokens(xs: string[]): Token[] {
  return xs.map((t) => ({
    kind: t.startsWith("`") ? "code" : "word",
    text: t,
  }));
}
