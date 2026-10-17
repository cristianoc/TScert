// A construction in a type's computed key is erased, and refused.
declare const C: { new <T extends string>(): object };
export function f(x: keyof { [new C<any>()]: number; a: number }): "a" {
  return x;
}
