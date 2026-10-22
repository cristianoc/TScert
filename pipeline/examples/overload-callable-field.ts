declare function pick(x: { readonly value: { tag: number } }): number;
declare function pick(x: {
  readonly value: (() => number) & { tag: number };
}): number;

export function example(x: {
  readonly value: (() => number) & { tag: number };
}): number {
  return pick(x);
}
