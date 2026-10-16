// Computed aliases with bounded parameters, applied within their bounds: an
// indexed access, `keyof`, a template literal, `typeof`, a conditional type,
// and an application inside a computed type.
type ElementOf<T extends readonly string[]> = T[number];
type KeysOf<T extends { a: number }> = keyof T;
type Greet<T extends "a" | "b"> = `hi ${T}`;
const box = { a: 1 };
type BoxOf<T extends string> = typeof box;
type P<T extends string> = T extends "a" ? T : never;
interface Box<T extends string> {
  a: T;
}
export function element(x: ElementOf<string[]>): string {
  return x;
}
export function keys(x: KeysOf<{ a: number; b: string }>): "a" | "b" {
  return x;
}
export function greet(x: Greet<"b">): "hi b" {
  return x;
}
export function boxed(x: BoxOf<string>): { a: number } {
  return x;
}
export function decided(x: P<"a" | "c">): "a" {
  return x;
}
export function operand(x: keyof Box<string>): "a" {
  return x;
}
// A declaration listed after the computed aliases, `String`'s, is named at
// its own position.
export function text(x: ElementOf<string[]>): string {
  return String(x);
}
