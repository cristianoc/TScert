// `JSON.stringify` calls a `toJSON` its argument holds: client code, which
// may shrink the array `map` visits. An object with a method is no JSON
// value, so the call is refused at the stated parameter.
export function wrong(xs: number[], o: { toJSON(): string }): number[] {
  return xs.map((x) => {
    JSON.stringify(o);
    return x;
  });
}
