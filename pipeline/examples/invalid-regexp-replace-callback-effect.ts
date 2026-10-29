// A replacement callback may write any location: one shrinking the array
// `map` steps leaves holes in its result, so it is no `string[]`.
export function wrong(xs: string[]): string[] {
  return xs.map((x) =>
    x.replace(/a/g, () => {
      xs.pop();
      return "";
    }),
  );
}
