// A write through a union must fit every arm. `false` fits the record's
// Boolean field and not the function's bag, which holds only `null`; after
// the write through `bag`, `n.value` is `false` where `null` is claimed
// (TypeScript writes a union's field at the union of its arms' types).
type Plain = { value: boolean };
type Nothing = ((x: boolean) => null) & { value: null };

function plain(seed: boolean): Plain {
  return { value: seed };
}
function nothing(): Nothing {
  return Object.assign<(x: boolean) => null, { value: null }>(
    (x: boolean): null => null,
    { value: null },
  );
}

export function wrong(flag: boolean, seed: boolean): null {
  const n = nothing();
  const bag: Plain | Nothing = flag ? plain(seed) : n;
  bag.value = false;
  return n.value;
}
