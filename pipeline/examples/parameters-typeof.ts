// Parameters of a function's typeof is its parameter list as a tuple: a
// required parameter a required position, an optional or defaulted one an
// optional position, a rest its rest; of a declared overload set, the last
// signature's. ConstructorParameters of a class's typeof is its
// constructor's list, and of a class declaring none, the empty list.
interface Options {
  depth: number;
}
declare function pick(n: number): string;
declare function pick(s: string, o?: Options): number;
function joined(sep: string, first: string = "", ...rest: string[]): string {
  return [first, ...rest].join(sep);
}
class Walker {
  depth: number;
  constructor(options?: Options) {
    this.depth = options ? options.depth : 0;
  }
}
class Plain {
  size: number = 0;
}
export function apply(): number {
  type Picked = Parameters<typeof pick>;
  type Joined = Parameters<typeof joined>;
  type Made = ConstructorParameters<typeof Walker>;
  type None = ConstructorParameters<typeof Plain>;
  const picked: Picked = ["a"];
  const joinedArgs: Joined = [",", "a", "b"];
  const made: Made = [{ depth: 2 }];
  const none: None = [];
  const options: NonNullable<Made[0]> = { depth: picked.length };
  return joinedArgs.length + new Walker(made[0]).depth + options.depth + none.length;
}
