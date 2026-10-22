export function copied(x: ({ k: "a" } | { k: "b" }) & { k: "a" }): { k: "a" } {
  return { ...x };
}
