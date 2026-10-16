// A parameter's object may be held by another reference at a type that leaves
// the key absent, or optional at another type: TypeScript accepts this module,
// and `seen` is "number number". A write adding a key through a parameter is
// refused on principle.
function bracketAssignOnStringIndex(x: { [k: string]: number }): void {
  x["newKey"] = 42;
}
function assignNumberToOptional(x: { opt?: number }): void {
  x.opt = 3;
}
const e = {};
const viewA: { newKey?: string; opt?: string } = e;
bracketAssignOnStringIndex(e);
assignNumberToOptional(e);
const seen: string = `${typeof viewA.newKey} ${typeof viewA.opt}`;
