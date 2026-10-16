class Wrapper<T extends { required: string }> {
  item: T;
  constructor(item: T) {
    this.item = item;
  }
  put(item: T): void {
    this.item = item;
  }
}

export function wrong(x: Wrapper<{ required: string; extra: number }>): void {
  if (x instanceof Wrapper) {
    x.put({ required: "yes" });
  }
}
