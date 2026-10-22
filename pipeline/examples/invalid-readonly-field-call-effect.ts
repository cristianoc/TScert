// A `readonly` field initialised with a function whose own body changes
// nothing, called in a `findIndex` callback. `readonly` is a view: it grants
// no write through it, and constrains neither another view of the same
// object nor which values the type holds. Any record with a `check` of the
// field's type is a `Test`, so the function called may shrink the list.
function positive(n: number): boolean {
  return n > 0;
}

export class Test {
  readonly check: typeof positive = positive;
}

export function first(test: Test, list: readonly number[]): number {
  return list.findIndex((n) => test.check(n));
}
