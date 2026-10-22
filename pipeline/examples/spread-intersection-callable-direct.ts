export function copied(x: (() => number) & { readonly tag: string }): {
  tag: string;
} {
  return { ...x };
}
