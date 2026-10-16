// A generic class's method has its instance as receiver: each ground
// application of the class has its own row, which its methods' receiver is.
import { Keeper } from "@fixture/lib";
export function keep(flag: boolean): boolean {
  return new Keeper<boolean>(flag).get();
}
export function count(n: number): number {
  const k = new Keeper<number>(n);
  return k.get();
}
