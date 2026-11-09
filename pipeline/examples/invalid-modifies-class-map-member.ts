// A class map with a member other than `values` and `stores`.
let cache: number | null = null;

export function cached(): Modifies<
  { "cell(cache)": { values: "init"; other: "any" } },
  number
> {
  cache ??= 1;
  return cache;
}
