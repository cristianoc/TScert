// Read by tests/compiler-api-shapes.mts, never run: JavaScript with JSDoc
// declarations, which a TypeScript source does not have.
/** @typedef {{ size: number }} Shape */
/** @typedef {Object} Record
 * @property {string} name
 * @property {number} [age]
 */
/** @callback Visitor @param {Shape} s @returns {void} */
/**
 * @template T, U
 * @typedef {{ first: T, second: U }} Both
 */
/**
 * @template {string} K
 * @typedef {Object} Keyed
 * @property {K} key
 */
/**
 * @template T
 * @callback Mapper
 * @param {T} x
 * @returns {T}
 */
export function local() {
  /** @typedef {number} Inner */
  /** @template T @typedef {T[]} List */
  return 1;
}
/** @template {string} K @template V
 * @param {K} k @param {V} v @returns {[K, V]} */
export function pair(k, v) { return [k, v]; }
/** @type {Shape} */
export const shape = { size: 1 };
/** @enum {number} */
export const Kinds = { A: 1 };
/** @import { Other } from "./other" */
/** @import * as data from "./data.json" with { type: "json" } */
export class Thing {
  /** @param {number} x */
  constructor(x) { /** @type {number} */ this.x = x; }
}
module.exports.extra = 1;
