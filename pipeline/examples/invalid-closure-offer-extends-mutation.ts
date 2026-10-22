// A closure over a base interface mapped over an array of an interface
// extending it, shrinking the array: `map` skips the index it removed, a
// hole in the `string[]`.
interface Base {
  readonly label: string;
}
interface Sized extends Base {
  readonly size: number;
}

export function wrong(xs: Sized[]): string[] {
  const label = (b: Base): string => {
    xs.pop();
    return b.label;
  };
  return xs.map(label);
}
