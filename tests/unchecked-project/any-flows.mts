/* Values typed `any`: where each must be reported, and the places that read
 * one as `unknown`, which must not be. */
import type { Json } from "../../tools/calculus.mts";

const text = '{"x":"oops"}';

// A library's `any` into a place typed otherwise, at the top.
export const parsed = JSON.parse(text); // expected: typed any
export const asNumber: number = JSON.parse(text); // expected: typed any
// A place typed `any` gives no guarantee: Object.assign stores the value
// into `target`, whose `x` then holds a string.
export function assigned(): number {
  const target = { x: 0 };
  Object.assign(target, JSON.parse(text)); // expected: typed any
  return target.x;
}
export const shown: string = String(JSON.parse(text)); // expected: typed any

// `any` deeper: a signature's result, a property, a type argument five deep.
export const parseNumber: (s: string) => number = JSON.parse; // expected: typed any
export function rejected(settled: PromiseRejectedResult): { reason: number } {
  return settled; // expected: typed any
}
export const nested: number[][][][][] = [[[[new Array(1)]]]]; // expected: typed any

// A construction of something other than the library's Map or Set.
interface Box<T> {
  value: T;
}
declare const Factory: new () => Box<any>; // expected: any
export const box: Box<number> = new Factory(); // expected: typed any
export const map: Map<string, number> = new Map();

// The receiver of `map` holds `any` inside; the callback's parameter is `any`.
export function lengths(v: unknown): number {
  if (Array.isArray(v)) return v.map((e) => e).length; // expected: typed any
  return v === null ? 0 : 1;
}

// Places reading `any` as `unknown`, and `JSON.parse` into parsed data.
export const data: unknown = JSON.parse(text);
export const json: Json = JSON.parse(text);
export const kind: string = typeof JSON.parse(text);
export function decoded(v: unknown): unknown[] {
  const entries: unknown[] = Array.isArray(v) ? v : [];
  return entries;
}
