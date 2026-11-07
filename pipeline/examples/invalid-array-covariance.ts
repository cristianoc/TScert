// TypeScript relates arrays covariantly, under every flag: `string[]` is
// accepted as `(string | number)[]`, and a write through the wider name puts a
// number in the array the narrower name still reads at `string`.
export function shout(xs: string[]): string[] {
  const ys: (string | number)[] = xs;
  ys.push(1);
  return xs.map((x) => x.toUpperCase());
}
