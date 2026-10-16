// A generic identity satisfies a monomorphic callable bound.
export function use(flag: boolean): boolean {
  const choose = <T extends (x: boolean) => boolean>(fn: T): T => fn;
  const id = <U>(value: U): U => value;
  return choose(id)(flag);
}

// Meeting an ordinary arrow bound does not require heap preservation.
export function capturedWrite(flag: boolean): boolean {
  const cell: { value: boolean } = { value: flag };
  const choose = <T extends (x: boolean) => boolean>(fn: T): T => fn;
  const id = <U>(value: U): U => {
    cell.value = !cell.value;
    return value;
  };
  return choose(id)(flag);
}
