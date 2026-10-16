// Where `x instanceof Box` fails, `x` may still be a `Box`: the class type is
// structural, and `{ v: 1 }` meets it without Box's prototype. TypeScript
// narrows the failed arm to `string` and would return the object as a string.
class Box {
  v: number;
  constructor(v: number) {
    this.v = v;
  }
}
export function label(x: Box | string): string {
  if (x instanceof Box) {
    return "box";
  }
  return x;
}
