type Box<T> = { value: T };
declare function make<T>(value: T): Box<T>;

export function widen(value: number): Box<unknown> {
  return make(value);
}
