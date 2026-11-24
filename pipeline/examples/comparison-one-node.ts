// A strict comparison evaluates each operand once, in source order, and
// branches on its own answer. Where it answers `true`, each operand narrows
// by the tags of the other's type: literals, a family against its
// singletons, an object by identity.

export function order(seen: number[]): number {
  const next = (k: 1 | 2): 1 | 2 => {
    seen.push(k);
    return k;
  };
  if (next(1) === next(2)) {
    return 0;
  }
  return seen.length;
}

export function family(s: string, k: "a" | "b"): "a" | "b" {
  if (s === k) {
    return s;
  }
  return k;
}

export function numberFamily(x: number, k: 1 | 2): 1 | 2 {
  if (x === k) {
    return x;
  }
  return k;
}

class Cat {
  meow: string = "";
}

export function object(a: string | Cat, b: Cat): string {
  if (a === b) {
    return a.meow;
  }
  return "";
}
