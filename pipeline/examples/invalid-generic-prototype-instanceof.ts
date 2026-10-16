class Cell<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
  put(v: T): void {
    this.v = v;
  }
}

export function incompatible(x: Cell<number>): number {
  if (x instanceof Cell) {
    x.put("wrong");
  }
  return x.v;
}
