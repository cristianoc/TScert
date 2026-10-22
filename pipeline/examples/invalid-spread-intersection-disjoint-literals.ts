// A key two operands state at types neither within the other: the copy's
// field would be their meet, here empty, which no one field states.
export function copied(x: { tag: number; k: "a" } & { k: "b" }): {
  tag: number;
} {
  return { ...x };
}
