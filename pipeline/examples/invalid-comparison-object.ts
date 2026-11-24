// Where `a === b` holds, `a` is the `Cat` `b` is, which has no `length`.
class Cat {
  meow: string = "";
}

export function f(a: string | Cat, b: Cat): number {
  if (a === b) {
    return a.length;
  }
  return 0;
}
