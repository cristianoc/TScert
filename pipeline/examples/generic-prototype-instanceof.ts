class Cell<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  put(v: T): void {
    this.v = v;
  }
}

export function typedIdentity(x: Cell<number>): number {
  if (x instanceof Cell) {
    x.put(3);
    return x.v;
  }
  return 0;
}

export function shadowed<T>(x: Cell<number>, value: T): T {
  if (x instanceof Cell) {
    x.put(3);
  }
  return value;
}

export function both(x: Cell<number>, y: Cell<string>): boolean {
  if (x instanceof Cell && y instanceof Cell) {
    x.put(3);
    y.put("ok");
    return true;
  }
  return false;
}

export function deferred(x: Cell<number>): () => boolean {
  return () => x instanceof Cell;
}

export function constructed(): boolean {
  const numbers = new Cell<number>(1);
  const strings = new Cell<string>("first");
  numbers.put(3);
  strings.put("next");
  return numbers instanceof Cell && strings instanceof Cell;
}

class Tagged<U extends string> {
  tag: U;
  constructor(tag: U) {
    this.tag = tag;
  }
  set(tag: U): void {
    this.tag = tag;
  }
}

export function bounded<U extends number>(x: Tagged<"ok">, value: U): U {
  if (x instanceof Tagged) {
    x.set("ok");
  }
  return value;
}

class Pair<L, R> {
  left: L;
  right: R;
  constructor(left: L, right: R) {
    this.left = left;
    this.right = right;
  }
  set(left: L, right: R): void {
    this.left = left;
    this.right = right;
  }
}

export function paired(x: Pair<number, string>): boolean {
  if (x instanceof Pair) {
    x.set(1, "ok");
    return true;
  }
  return false;
}
