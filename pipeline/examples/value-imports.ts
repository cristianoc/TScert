// Imported values at the types their declarations state: a function, an
// annotated constant, and a class constructed with `new`. The result is
// relative to those assumptions.
import { Counter, double, limit } from "@fixture/lib";
const start: number = double(limit);
export function next(): number {
  const c = new Counter(start);
  return c.bump();
}
