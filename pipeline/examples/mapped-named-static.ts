// A mapped record substitutes the parameter inside its constructor's static field.
interface Box<T> {
  readonly ctor: { new (): { x: number }; readonly value: T };
}
type Wrapped<U> = Readonly<Box<number>>;
class Numeric {
  static readonly value: number = 7;
  x: number = 0;
}
export function input(box: Wrapped<string>): number {
  return box.ctor.value;
}
export function output(): Wrapped<string> {
  return { ctor: Numeric };
}
