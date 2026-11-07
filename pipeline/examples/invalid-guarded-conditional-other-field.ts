// A conditional testing another field before a read a guarded clause bounds:
// the clause bounds `hyphens` only where `contexts` is not `null`, and
// `items.extra === null` frees no guard of `contexts`, so the read is refused
// (run under Node: `hyphenAfterOtherTest({ contexts: null, extra: [],
// hyphens: [] }, 0)` reads `undefined` at `number`).

export type Items = {
  contexts: number[] | null;
  extra: number[] | null;
  hyphens: number[];
};

/**
 * @requires safeInteger(index) && 0 <= index
 * @requires items.contexts === null || index < items.hyphens.length
 */
export function hyphenAfterOtherTest(items: Items, index: number): number {
  return items.extra === null ? 0 : items.hyphens[index]!;
}

/**
 * @requires safeInteger(index) && 0 <= index
 * @requires items.contexts === null || index < items.hyphens.length
 */
export function hyphenAfterOwnTest(items: Items, index: number): number {
  return items.contexts === null ? 0 : items.hyphens[index]!;
}
