// Minus reads Values<[number, number]>: `toArray()` and
// `getUnique()` give `[number, number] & DepSafe`, the meet of the tuple with
// DepSafe's alternatives, which is below each side: its elements are read as
// the tuple's, the array is sorted and reduced, and the value is Managed.
// The meet is one object, the array shape with Managed's symbol key, which
// an array may own (SOURCE-MODEL.md, "Arrays").
import type { Managed, Mapper, Values } from "@fixture/collections";
class Minus implements Mapper<string, [number, number], string, number> {
  mapEntry(
    key: string,
    values: Values<[number, number]>,
  ): Iterable<[string, number]> {
    const acc = (p: number | null, c: [number, number]) => {
      return p !== null ? p - c[1] : c[1];
    };
    return [
      [key, values.toArray().sort().reduce<number | null>(acc, null) ?? 0],
    ];
  }
}
class First {
  of(values: Values<[number, number]>): number {
    return values.getUnique()[0];
  }
}
export function minus(
  values: Values<[number, number]>,
): Iterable<[string, number]> {
  return new Minus().mapEntry("k", values);
}
export function first(values: Values<[number, number]>): number {
  return new First().of(values);
}
export function second(values: Values<[number, number]>): number {
  return values.getUnique()[1];
}
export function managed(values: Values<[number, number]>): Managed {
  return values.getUnique();
}
