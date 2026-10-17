// The fresh-storage controls at a result type admitting holes: each callback
// pops the mapped array through an alias, a join of a fresh and the mapped
// array, a reassigned variable, or a helper's parameter, so `map` takes its
// signature with holes, which `(string | undefined)[]` admits. A callback
// claimed within `{value: any, store: keep}` is refused at each.
function drop(a: string[]): void {
  a.pop();
}

export function aliased(xs: string[]): (string | undefined)[] {
  return xs.map((x) => {
    const a = xs;
    a.pop();
    return x;
  });
}

export function joined(xs: string[]): (string | undefined)[] {
  return xs.map((y) => {
    const a = y.length > 1 ? y.split("") : xs;
    a.pop();
    return y;
  });
}

export function reassigned(xs: string[]): (string | undefined)[] {
  return xs.map((z) => {
    let a = z.split("");
    a = xs;
    a.pop();
    return z;
  });
}

export function dropped(xs: string[]): (string | undefined)[] {
  return xs.map((w) => {
    drop(xs);
    return w;
  });
}
