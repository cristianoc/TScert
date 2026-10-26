// A mapped record substitutes the parameter inside its constructor's static field.
interface Box<T> {
  readonly ctor: { new (): { x: number }; readonly value: T };
}
type Wrapped<U> = Readonly<Box<number>>;
class Textual {
  static readonly value: string = "wrong";
  x: number = 0;
}
export function output(): Wrapped<string> {
  return { ctor: Textual };
}
