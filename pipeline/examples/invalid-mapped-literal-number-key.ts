// Rule mapped-literal-keys: the field `1` holds the number 1, not the string "1".
type Lit<K extends PropertyKey> = { [P in K]: P };

export function make(): Lit<"a" | 1> {
  // @ts-expect-error Type 'string' is not assignable to type '1'
  return { a: "a", 1: "1" };
}
