// A generic class: its binders are parameter rows of the initialization
// unit, which certifies the constructor and the methods at every assignment of
// them; a unit using the class names the instance it constructs.
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  get(): T {
    return this.v;
  }
  put(v: T): void {
    this.v = v;
  }
}

class Pair<A, B> {
  left: A;
  right: B;
  constructor(left: A, right: B) {
    this.left = left;
    this.right = right;
  }
  first(): A {
    return this.left;
  }
}

export function numbers(n: number): number {
  const b = new Box(n);
  b.put(2);
  return b.get();
}

export function strings(s: string): string {
  const b = new Box(s);
  return b.get();
}

export function pairs(n: number, s: string): number {
  const p = new Pair(n, s);
  return p.first();
}
