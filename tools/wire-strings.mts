/** Every string a wire document holds is well-formed Unicode: no lone
 * surrogate, in a key or a value (HOST-FAMILIES.md, "Tag sets", and the rule
 * each decoder states). A JavaScript string may hold one, which
 * `JSON.stringify` writes as a `\ud800` escape; Lean's JSON parser would read
 * it as U+FFFD, a different string, and OCaml's refuses it. So the writers
 * refuse such a string and every reader refuses a document holding one,
 * before reading any value. */

import { passToolFailure } from "./thrown.mts";

/** Whether a string is well-formed UTF-16: each surrogate in a pair. */
export function wellFormed(s: string): boolean {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c >= 0xd800 && c <= 0xdbff) {
      const d = s.charCodeAt(i + 1);
      if (!(d >= 0xdc00 && d <= 0xdfff)) return false;
      i++;
    } else if (c >= 0xdc00 && c <= 0xdfff) return false;
  }
  return true;
}

/** The first string of a parsed JSON value, key or value, that is not
 * well-formed, with the source span of the nearest enclosing object stating
 * one (`pos`), where any does. */
export function illFormedString(value: unknown, pos: unknown = null): { text: string; pos: unknown } | null {
  if (typeof value === "string") return wellFormed(value) ? null : { text: value, pos };
  if (Array.isArray(value)) {
    for (const x of value) {
      const found = illFormedString(x, pos);
      if (found) return found;
    }
    return null;
  }
  if (value !== null && typeof value === "object") {
    const here = "pos" in value ? value.pos : pos;
    for (const [k, x] of Object.entries(value)) {
      if (!wellFormed(k)) return { text: k, pos: here };
      const found = illFormedString(x, here);
      if (found) return found;
    }
  }
  return null;
}

/** Refuse a document holding a string that is not well-formed Unicode. */
export function requireWellFormed(value: unknown, what: string): void {
  const refusal = wellFormedRefusal(value, what);
  if (refusal !== null) throw Error(refusal);
}
/** The refusal of a document holding a string that is not well-formed
 * Unicode, the first in document order, or null. */
export function wellFormedRefusal(value: unknown, what: string): string | null {
  const found = illFormedString(value);
  return found ? `${what}: a string that is not well-formed Unicode, a lone surrogate, is refused` +
    (Array.isArray(found.pos) ? ` (at [${found.pos.join(",")}))` : "") : null;
}

/** A wire document's bytes as text, refused where they are not valid UTF-8:
 * Node's own decoding would read an invalid sequence as U+FFFD. */
export function wireText(bytes: Uint8Array, what: string): string {
  try {
    return new TextDecoder("utf-8", { fatal: true }).decode(bytes);
  } catch (error) {
    passToolFailure(error);
    throw Error(`${what}: the text is not valid UTF-8`);
  }
}
