// A generic method whose parameter holds a plain method: the contract is
// represented whole, so a value of it is passed through.
interface Runner {
  run<P extends unknown[]>(
    helper: { id(x: number): number },
    ...args: P
  ): number;
}

export function pass(r: Runner): Runner {
  return r;
}
