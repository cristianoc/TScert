// A method typed `never` that shrinks the array it is handed, then throws,
// called in a `map` callback that catches the throw: the call never returns
// normally, but its throw reaches the handler, and the method's signature
// bounds no heap on a throw. The result may hold holes and is not
// `number[]` (run under Node: `map` skips the index the method removed).
export class Bump {
  bump(xs: number[]): never {
    xs.pop();
    throw new Error("bumped");
  }
}

export function wrong(b: Bump, xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    try {
      b.bump(xs);
    } catch {
      return x;
    }
  });
  return r;
}
