type First = { k: string | number } & { k: string | boolean };
export function last(x: First & { k: string }): { k: string } {
  return { ...x };
}
export function first(x: { k: string } & First): { k: string } {
  return { ...x };
}
export function middle(
  x: { k: string | number } & { k: string } & { k: string | boolean },
): { k: string } {
  return { ...x };
}
export function callable(x: (() => number) & { tag: string }): { tag: string } {
  return { ...x };
}
