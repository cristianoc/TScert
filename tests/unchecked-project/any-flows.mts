/* Values typed `any`: the program is checked over its external declarations
 * read at their contracts (tools/shadow-contracts.mts), and each error there
 * is an `any flow`; a value still typed `any` is `typed any`. */
import type { Json } from "../../tools/calculus.mts";
import type { Expression } from "../../tools/node_modules/typescript/dist/ast/index.js";
import { Factory, consume, foreign, invoke, invokeAll, keyed, type Box } from "./library/index.mjs";

const text = '{"x":"oops"}';

// `JSON.parse` of a text is parsed data, not a number or a parser of numbers.
export const parsed: Json = JSON.parse(text);
export const asNumber: number = JSON.parse(text); // expected: any flow
export const parseNumber: (s: string) => number = JSON.parse; // expected: any flow
export const shown: string = String(JSON.parse(text));
export const data: unknown = JSON.parse(text);
export const kind: string = typeof JSON.parse(text);

// A library's results, properties, index signatures and callback parameters.
export function rejected(settled: PromiseRejectedResult): { reason: number } {
  return settled; // expected: any flow
}
export const nested: number[][][][][] = [[[[new Array(1)]]]]; // expected: any flow
export const box: Box<number> = new Factory(); // expected: any flow
export const property: { x: number } = foreign; // expected: any flow
export const dictionary: { [key: string]: number } = foreign; // expected: any flow
export const numbered: { [key: number]: number } = keyed; // expected: any flow
export const sink: (f: (x: number) => void) => void = invoke; // expected: any flow
export const sinkAll: (f: (x: number) => void) => void = invokeAll; // expected: any flow
// An input typed `any` with no reviewed contract.
consume(1); // expected: any flow

// The compiler's brands read as optional `unknown` (reading rule 2).
export function branded(e: Expression): { _expressionBrand: number } {
  return e; // expected: any flow
}

// An empty map is a map at the place's types; the callback's parameter of
// `map` over an `Array.isArray` narrowing is `unknown`.
export const map: Map<string, number> = new Map();
export function lengths(v: unknown): number {
  if (Array.isArray(v)) return v.map((e) => e).length;
  return v === null ? 0 : 1;
}

// A value still typed `any`: a written one, and an array no annotation types.
declare const written: any; // expected: any, typed any
export const rewritten: number = written; // expected: typed any
export function evolving(): number {
  const xs = []; // expected: typed any
  xs.push(1); // expected: typed any
  return xs.length; // expected: typed any
}

// Outside the check: `Object.assign` overwrites `target.reason` with the
// rejection's reason, a string, in a program with no `any` (mutation safety
// is TScert's, not this check's).
export function corrupt(r: PromiseRejectedResult): number {
  const target = { reason: 0 };
  Object.assign(target, r);
  Object.assign<{ reason: number }, PromiseRejectedResult>(target, r);
  Object.assign(target, (r));
  Object.assign(target, JSON.parse(text));
  return target.reason;
}
