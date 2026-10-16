// Generic imported values at the instances their calls name: a function, and
// a class constructed with explicit type arguments. An inherited field is
// part of the instance type.
import { Holder, Named, generic } from "@fixture/lib";
export function use(x: number): number {
  return generic(x);
}
export function hold(flag: boolean): boolean {
  const h = new Holder<boolean>(flag);
  return h.value;
}
export function inherited(): number {
  return new Named().tag;
}
