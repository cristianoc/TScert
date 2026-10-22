// The element's method requires a receiver with size. A closure over Base
// may call step on a receiver holding only label, so it is offered no
// signature at Counter. Under Node the method reads the absent size.
interface Base {
  readonly label: string;
  step(this: { readonly label: string }): number;
}
interface Counter extends Base {
  step(this: { readonly label: string; readonly size: number }): number;
}

export function wrong(xs: Counter[]): number[] {
  const once = (b: Base): number => b.step();
  return xs.map(once);
}
