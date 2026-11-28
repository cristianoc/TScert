// Rule mapped-literal-keys: over a union of literals, each field's key is the
// literal itself, so the field `1` holds the number 1.
type Lit<K extends PropertyKey> = { [P in K]: P };

export function make(): Lit<"a" | 1> {
  return { a: "a", 1: 1 };
}
