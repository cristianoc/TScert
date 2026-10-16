// An overloaded guard narrows by the overload its actuals select: the
// second actual, "number", selects the promise `x is number`.
import { isKind } from "@fixture/lib";

export function value(x: unknown): number {
  if (isKind(x, "number")) return x;
  return 0;
}
