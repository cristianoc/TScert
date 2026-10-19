// Read by tests/compiler-api-shapes.mts, never run: a TypeScript source
// exercising the syntax tree's node kinds, JSDoc included, beside the
// repository's own sources.
/**
 * A documented declaration.
 * @template T the element
 * @template {string} K a constrained key
 * @param {T} x the value
 * @param y the other value
 * @returns {T} the value
 * @throws {Error} never
 * @see other
 * @link other
 * @deprecated
 * @example f(1)
 * @typedef {object} Shape
 * @property {number} size
 * @callback Visitor
 * @this {object}
 * @augments Base
 * @implements Iface
 * @public
 * @private
 * @protected
 * @readonly
 * @override
 * @satisfies {object}
 * @overload
 * @import { a } from "b"
 * @type {number}
 * @enum {number}
 */
export function documented<T, K extends string = string>(x: T, y?: K): T {
  return y === undefined ? x : x;
}

declare const decorate: (target: unknown, context: unknown) => void;

export abstract class Base<T> implements Iface {
  static #count = 0;
  #secret = 1;
  protected readonly field: T | undefined;
  declare ambient: number;
  accessor stored = 0;
  static {
    Base.#count++;
  }
  constructor(public readonly x: number, private y?: string) {
    this.field = undefined;
  }
  get value(): number {
    return this.#secret + this.x;
  }
  set value(v: number) {
    this.#secret = v;
  }
  abstract shape(): string;
  method?(): void;
  [key: string]: unknown;
  @decorate
  decorated(): void {}
}

export interface Iface {
  readonly x: number;
  (a: number): string;
  new (a: string): Iface;
  method?<T>(a: T): T;
  [index: number]: unknown;
}

export type Mapped<T> = { readonly [K in keyof T]?: T[K] };
export type Conditional<T> = T extends string ? "s" : T extends infer U extends number ? U : never;
export type Template = `a${string}b${number}`;
export type Tuple = [first: string, second?: number, ...rest: boolean[]];
export type Operators = keyof Iface | typeof documented | Iface["x"] | readonly string[] | unique symbol;
export type Functions = ((a: number) => void) & (new (a: string) => object) & abstract new () => object;
export type Literals = 1 | -1 | "s" | true | false | null | undefined | 1n | void | never | unknown | any | object | bigint | symbol;
export type Predicate = (x: unknown) => x is string;
export type Asserts = (x: unknown) => asserts x is string;
export type AssertsThis = (this: Iface) => asserts this;
export type Imported = import("./other").Shape;
export type Paren = (string);
export type Optional = Tuple extends [infer A, ...infer B] ? [A, B] : never;

export enum Color {
  Red,
  Green = 2,
  Blue = "blue",
}
export const enum Flags {
  None = 0,
  One = 1 << 0,
}

export namespace Space {
  export const inner = 1;
  export namespace Deeper.Deepest {
    export type T = number;
  }
}
declare module "ambient-module" {
  export const value: number;
}
declare global {
  interface Window {
    extra?: number;
  }
}

import type { Other } from "./other";
import * as everything from "./other";
import defaultExport, { named as renamed, type typeOnly } from "./other";
import json from "./data.json" with { type: "json" };
import fs = require("fs");
export { renamed as reexported };
export * from "./other";
export * as all from "./other";
export type { Other };
export default documented;
export import alias = Space.inner;

label: for (let i = 0, j = 10; i < j; i++, j--) {
  if (i % 2) continue label;
  else if (i > 5) break label;
}
for (const key in { a: 1 }) void key;
for (const [k, v] of Object.entries({ a: 1 })) void (k + v);
async function asynchronous(): Promise<void> {
  for await (const x of [Promise.resolve(1)]) void x;
  await Promise.resolve();
}
function* generator(): Generator<number, void, unknown> {
  yield 1;
  yield* [2, 3];
}
let n = 0;
while (n < 3) n++;
do n--; while (n > 0);
switch (n) {
  case 0:
    break;
  default:
}
try {
  throw new Error("e");
} catch (e) {
  void e;
} finally {
  n = 1;
}
try {
  n = 2;
} catch {
  n = 3;
}
with0: {
  debugger;
}
const object = { a: 1, "b": 2, [`c`]: 3, n, ...{ d: 4 }, method() { return this.a; }, get g() { return 1; }, set s(v: number) {} };
const { a, b: renamedB = 1, ...restObject } = object;
const [first, , third = 3, ...restArray] = [1, 2, 3, 4];
const arrow = async <T,>(x: T): Promise<T> => x;
const fn = function named(this: unknown, ...args: number[]): number { return args.length; };
const classExpression = class Named<T> extends Base<T> { shape(): string { return ""; } };
const operators = [
  -n, +n, !n, ~n, ++n, n--, typeof n, void n, delete (object as { a?: number }).a,
  n ** 2, n * 2 / 2 % 2, n + 1 - 1, n << 1 >> 1 >>> 1, n < 1, n > 1, n <= 1, n >= 1,
  object instanceof Object, "a" in object, n == 1, n != 1, n === 1, n !== 1, n & 1, n | 1, n ^ 1,
  n && 1, n || 1, n ?? 1, n ? 1 : 2, (n = 1), (n += 1), (n -= 1), (n *= 1), (n /= 1), (n %= 1), (n **= 1),
  (n <<= 1), (n >>= 1), (n >>>= 1), (n &= 1), (n |= 1), (n ^= 1), (n &&= 1), (n ||= 1), (n ??= 1), (n, 1),
];
const access = [object?.a, object["a"], object?.["a"], fn?.(1), new Date(), String.raw`x${n}y`, `a${n}b${n}c`, `plain`, /re+/gi, 1_000, 0x10, 1e3, 10n];
const casts = [n as number, <number>n, n!, n satisfies number, object as const];
const jsx = undefined;
export { asynchronous, generator, arrow, classExpression, operators, access, casts, jsx, first, third, restArray, a, renamedB, restObject, everything, defaultExport, json, fs };
