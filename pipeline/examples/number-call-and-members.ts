// `Number` both called and read through its members: a callable object with
// methods, its call signature and each method the reviewed overlay's.
function parse(text: string): number {
  const n = Number(text);
  return Number.isFinite(n) ? n : 0;
}
