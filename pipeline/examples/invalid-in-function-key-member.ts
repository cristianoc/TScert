// A passed `"call" in x` keeps the open record arm, which may own `call` at
// any type: TypeScript narrows `x` to `Caller` and types `x.call()` as a
// number. Under Node, `wrong({ size: 1, call: () => "s" })` returns "s".
class Caller {
  call(): number {
    return 1;
  }
}

export function wrong(x: Caller | { size: number }): number {
  return "call" in x ? x.call() : x.size;
}
