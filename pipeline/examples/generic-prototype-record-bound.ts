class Wrapper<T extends { required: string }> {
  item: T;
  constructor(item: T) {
    this.item = item;
  }
  getItem(): T {
    return this.item;
  }
}

export function inspect(x: Wrapper<{ required: string }>): boolean {
  return x instanceof Wrapper;
}

type Text = string;
type Required = { required: string };

class Named<R extends Required> {
  item: R;
  constructor(item: R) {
    this.item = item;
  }
  getItem(): R {
    return this.item;
  }
}

class Tagged<U extends Text> {
  value: U;
  constructor(value: U) {
    this.value = value;
  }
  get(): U {
    return this.value;
  }
}

export function named(x: Named<Required>): string {
  if (x instanceof Named) {
    return x.getItem().required;
  }
  return "";
}

export function primitiveAlias(x: Tagged<string>): string {
  if (x instanceof Tagged) {
    return x.get();
  }
  return "";
}
