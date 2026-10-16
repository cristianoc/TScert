class Wrapper<T extends { required: string }> {
  item: T;
  constructor(item: T) {
    this.item = item;
  }
  getItem(): T {
    return this.item;
  }
}

export function read(): number {
  const wrapped = new Wrapper({ required: "yes", extra: 42 });
  return wrapped.getItem().extra;
}
