// A string's length read through a field survives a call whose closed
// footprint only initializes values: the field's location holds a string,
// which `init` keeps, so the call respects the fact's support
// (FOOTPRINTS.md, "Supports of index facts").
type R = { name: string };

function setup(o: { c: number | undefined }): Modifies<{ values: "init"; stores: "keep" }, void> {
  o.c ??= 1;
}

/** @requires safeInteger(i) && 0 <= i && i < s.length */
function at(s: string, i: number): number {
  return s.codePointAt(i)!;
}

/** @requires safeInteger(i) && 0 <= i && i < r.name.length */
export function f(r: R, o: { c: number | undefined }, i: number): number {
  setup(o);
  return at(r.name, i);
}
