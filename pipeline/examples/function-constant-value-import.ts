// An imported constant holding a function literal is read at the literal's
// annotations, as a function declaration is: a plain one, a generic one and
// a function expression.
import { halve, head, named } from "@fixture/lib";

export function use(xs: readonly number[]): number {
  return halve(head(xs) ?? 0) + named("a").length;
}
