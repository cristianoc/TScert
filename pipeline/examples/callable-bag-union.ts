// A union of a record and a function carrying the same field: reading and
// writing the field eliminate the union, each arm by its own rule, the
// function's through its bag.
type Plain = { value: boolean };
type Callable = ((x: boolean) => boolean) & { value: boolean };

function plain(seed: boolean): Plain {
  return { value: seed };
}
function callable(seed: boolean): Callable {
  return Object.assign<(x: boolean) => boolean, { value: boolean }>(
    (x: boolean): boolean => x,
    { value: seed },
  );
}

export function readWrite(flag: boolean, seed: boolean): boolean {
  const bag: Plain | Callable = flag ? plain(seed) : callable(seed);
  bag.value = false;
  return bag.value;
}
