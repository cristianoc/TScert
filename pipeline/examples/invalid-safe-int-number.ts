// A `number` passed where `SafeInt` is declared: `number` is not within the
// safe integers, so the call is refused. The refusal is of the type
// contract, not of a run: no step reads the value as an integer here.
function keep(i: SafeInt): SafeInt {
  return i;
}

export function pass(x: number): SafeInt {
  return keep(x);
}
