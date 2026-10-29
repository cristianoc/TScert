// A loop over an array a dictionary's key holds, tested before the loop:
// the iterator's separation covers the fields records name, not a
// dictionary's keys, so a step keeps no read link about the key, and the
// loop's cuts claim none. The body's own guard narrows each element.
// Census functions:
// diagnostic.mts#knowledge.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function nat(v: Json | undefined): void {
  if (typeof v !== "number" || v < 0) throw Error("index");
}
export function partners(f: Fields): void {
  if (!Array.isArray(f.partners)) throw Error("partners");
  for (const p of f.partners) {
    if (!Array.isArray(p)) throw Error("partner");
    nat(p[0]);
  }
}
