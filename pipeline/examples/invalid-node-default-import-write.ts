// A member of `node:path`'s object written through its default import: the
// member is read as the named export it holds, which no code replaces. A
// replaced `dirname` that shrinks the array `map` visits leaves a hole (run
// under Node): the write is refused where it is written.
import path from "node:path";
export function hook(xs: string[]): void {
  path.dirname = (p: string): string => {
    xs.pop();
    return p;
  };
}
export function parents(xs: string[]): string[] {
  return xs.map((x) => path.dirname(x));
}
