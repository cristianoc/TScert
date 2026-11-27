// Native `RegExp.prototype.test` and `exec` framing:
// - A non-global, non-sticky regex literal or `const` regex states the empty
//   footprint, certifying `Modifies<{}, boolean>` and preserving quantified
//   array invariants across the call.
// - A global, sticky or conservative `RegExp` states `{this.lastIndex: scalar}`,
//   a receiver-scoped field region disjoint from array spines, array element
//   cells and unrelated fields, so quantified array invariants and unrelated
//   field narrowings survive `re.test(s)` and `re.exec(s)`.

const digitsRe = /^[0-9]+$/u;
const globalWordRe = /[a-z]+/g;

export function isDigits(s: string): Modifies<{}, boolean> {
  return digitsRe.test(s) || /^[0-9]+$/.test(s);
}

/**
 * @requires forall i in rows: rows[i] === null || 1 <= rows[i].length
 */
export function sumFirstAcrossRegExpTests(
  rows: Dense<(Dense<number[]> | null)[]>,
  texts: Dense<string[]>,
  re: RegExp,
): number {
  let total = 0;
  /**
   * @invariant safeInteger(i) && 0 <= i
   * @invariant forall k in rows: rows[k] === null || 1 <= rows[k].length
   */
  for (let i = 0; i < rows.length; i++) {
    const t = i < texts.length ? texts[i]! : "";
    if (digitsRe.test(t) || /^[a-z]+$/u.test(t) || re.test(t) || globalWordRe.test(t)) {
      const row = rows[i] ?? null;
      if (row !== null) total += row[0]!;
    }
  }
  return total;
}

type Cursor = { i: number; label: string | null };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length */
export function cursorAcrossRegExpTest(
  re: RegExp,
  c: Cursor,
  xs: Dense<number[]>,
  s: string,
): number {
  if (c.label !== null) {
    if (re.test(s) && re.exec(s) !== null) return xs[c.i]! + c.label.length;
    return xs[c.i]!;
  }
  return 0;
}
