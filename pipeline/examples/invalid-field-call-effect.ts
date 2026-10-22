// A `findIndex` callback calling a function held by a class field: the
// field's contract is its annotation, an ordinary arrow, so a call through
// it may change any storage, and the callback is the unrestricted one,
// whose element is `number | undefined`. Whatever function the field was
// initialised with, the value read at the call is any function of that
// type: one written there later shrinks the list and is handed `undefined`.
function positive(n: number): boolean {
  return n > 0;
}

export class Test {
  check: typeof positive = positive;
}

export function first(test: Test, list: readonly number[]): number {
  return list.findIndex((n) => test.check(n));
}
