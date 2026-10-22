declare function pick(x: { readonly length?: number }): number;
declare function pick(x: { readonly length: number }): number;

export function example(x: { readonly length: number }): number {
  return pick(x);
}
