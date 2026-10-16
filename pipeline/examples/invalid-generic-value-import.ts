// A generic imported function's instance returns its instantiated type.
import { generic } from "@fixture/lib";
export function wrong(x: number): boolean {
  return generic(x);
}
