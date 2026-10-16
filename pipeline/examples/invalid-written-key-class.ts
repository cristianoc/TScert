// A class expression in a type's computed key, its heritage calling a
// generic function: erased, and refused at the key.
type B<T extends string> = T;
declare function make<T>(): { new (): object };
export function f(
  x: keyof { [class extends make<B<any>>() {}]: number; a: number },
): "a" {
  return x;
}
