// `path` imported by default from `node:path`: the module's object, read
// through its members, each the named export it holds; `basename` and `sep`
// are read through their reviewed entries. TypeScript declares `path` twice,
// a namespace of types and the constant its value is: each member read is
// the constant's member.
// Census functions:
// shadow-contracts.mts#shadowText, unchecked.mts#check, unchecked.mts#findIn.
import path from "node:path";
export function use(s: string): string {
  return path.basename(s);
}
export function parts(s: string): string[] {
  return s.split(path.sep);
}
