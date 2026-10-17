// A replacer is client code `JSON.stringify` calls on every member: it may
// shrink the array `map` visits. The call is read with the value only.
export function wrong(
  xs: number[],
  replacer: (key: string, value: unknown) => unknown,
): number[] {
  return xs.map((x) => {
    JSON.stringify(x, replacer);
    return x;
  });
}
