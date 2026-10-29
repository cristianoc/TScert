// `node:path`'s object read as a value through its default import: the
// alias writes a member, replacing `dirname` by a function that shrinks the
// array `map` visits, which leaves a hole (run under Node). The default
// import is read through member reads alone: the value read is refused.
import path from "node:path";
export function hook(xs: string[]): void {
  const object = path;
  object.dirname = (p: string): string => {
    xs.pop();
    return p;
  };
}
export function parents(xs: string[]): string[] {
  return xs.map((x) => path.dirname(x));
}
