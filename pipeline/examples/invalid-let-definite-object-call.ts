// A call between the write and the read may run a closure that writes the
// cell: the fact is forgotten, and the read is at the contract, which
// admits `undefined`. TypeScript accepts it.
interface Point {
  x: number;
  y: number;
}

export function afterCall(flag: boolean, log: () => void): Point {
  let p: Point;
  const reset = () => {
    p = { x: 0, y: 0 };
  };
  p = { x: 1, y: 2 };
  log();
  reset();
  return p;
}
