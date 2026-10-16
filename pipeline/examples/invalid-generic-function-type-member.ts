// A method returning a generic function type is not met by one returning a
// generic function of another result: refused at the result's obligation.
interface Twice {
  twice(): <A>(x: A) => [A, A];
}

interface Once {
  twice(): <A>(x: A) => A;
}

export function wrong(t: Once): Twice {
  // @ts-expect-error
  return t;
}
