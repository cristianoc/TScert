type Tagged = (() => number) & { readonly tag: string };
export function copied(x: Tagged): { tag: string } {
  return { ...x };
}
