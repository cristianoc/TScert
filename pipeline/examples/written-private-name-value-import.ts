// An imported class with a private field: its name `#x` is a declaration's
// name, no expression.
import { Private } from "@fixture/lib";
export function f(x: Private): number {
  return x.a;
}
