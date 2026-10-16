// An array may carry own keys its prototype does not provide, as a library
// may mark the arrays it manages with a hidden key: a tuple that is also a
// `Managed` record is inhabited, its elements and its marker both hold, and it
// is both a tuple and a `Managed`.
import { isManaged, managedPair, type Managed } from "@fixture/lib";
export function first(xs: [number, number] & Managed): number {
  return xs[0];
}
function sum(xs: [number, number]): number {
  return xs[0] + xs[1];
}
export function asTuple(xs: [number, number] & Managed): number {
  return sum(xs);
}
export function asManaged(xs: [number, number] & Managed): true {
  return isManaged(xs);
}
export function methods(xs: [number, number] & Managed): number {
  return xs.reduce((acc: number, x: number): number => acc + x, 0);
}
export function fresh(): number {
  return first(managedPair());
}
