// A file declaring its own `SafeInt`: an ordinary type alias of `number`,
// so a `number` passes where it is written.
type SafeInt = number;

function keep(i: SafeInt): SafeInt {
  return i;
}

export function pass(x: number): SafeInt {
  return keep(x);
}
