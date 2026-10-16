// An untyped ambient field holds whatever the code outside put there: not a
// string TypeScript's `any` would let it be read as.
declare class Untyped {
  pub;
}
function readAsString(x: Untyped): string {
  const s: string = x.pub;
  return s;
}
