// A spread of a program's iterable after an operand that runs code: its
// iterator's code would run before that call, where the lowering places the
// protocol, and not after it, where JavaScript runs it.
function sum(...xs: number[]): number {
  return xs.length;
}

function first(): number {
  return 1;
}

export function spread(values: Iterable<number>): number {
  return sum(first(), ...values);
}
