interface Ref<T> {
  contents: T;
}
export function read<U, T extends Ref<U>>(x: T & object): U {
  return x.contents;
}
export function chain<U, T extends Ref<U>, V extends T>(x: V): U {
  return x.contents;
}
export function write<U, T extends Ref<U>>(x: T, value: U): U {
  x.contents = value;
  return x.contents;
}
export function closure<U>(value: U): U {
  const get = <T extends Ref<U>>(x: T): U => x.contents;
  return get({ contents: value });
}
export function use(): string {
  return read({ contents: "ok" });
}
