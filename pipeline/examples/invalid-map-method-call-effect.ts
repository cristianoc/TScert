// A `map` callback calling a method of a class instance, its result bound at
// an annotation without holes: the method's contract is its signature, which
// states no effect, so the call may change any storage and `map` takes its
// signature with holes. A value of the class's type whose `local` shrinks
// the mapped array leaves a hole in the result.
export class Names {
  prefix: string = "";
  local(n: string): string {
    return this.prefix + n;
  }
}

export function wrong(names: Names, xs: string[]): string[] {
  const r: string[] = xs.map((n) => names.local(n));
  return r;
}
