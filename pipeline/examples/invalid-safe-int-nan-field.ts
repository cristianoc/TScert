// `NaN` written into a field typed `SafeInt`: the location's contract is
// established at every write, and `NaN` is no integer, so the write is
// refused. The refusal is of the type contract: under Node, after
// `reset(c)`, `count(c)` returns `NaN` at `SafeInt`.

type Counter = { count: SafeInt };

export function reset(c: Counter): void {
  c.count = NaN;
}

export function count(c: Counter): SafeInt {
  return c.count;
}
