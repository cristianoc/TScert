// The unsafe neighbour of `call-path-string-length-kept`: a call whose
// footprint changes values arbitrarily may replace `r.name`, so
// `i < r.name.length` does not survive it (run under Node with r.name = "ab"
// and i = 1: `at` returns `undefined`, no number).
type R = { name: string };

function shorten(r: R): Modifies<{ values: "any"; stores: "keep" }, void> {
  r.name = "";
}

/** @requires safeInteger(i) && 0 <= i && i < s.length */
function at(s: string, i: number): number {
  return s.codePointAt(i)!;
}

/** @requires safeInteger(i) && 0 <= i && i < r.name.length */
export function f(r: R, i: number): number {
  shorten(r);
  return at(r.name, i);
}
