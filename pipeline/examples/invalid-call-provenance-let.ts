// A `let` written with a parameter holds a function the caller supplies, which
// may own a `call` property returning a string.
type Host = { value: number };

function reassigned(f: (this: Host) => number, source: Host): number {
  let g = function (this: Host): number {
    return this.value;
  };
  g = f;
  return g.call(source);
}
