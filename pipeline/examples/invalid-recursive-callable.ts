// A view of `R`'s bag that also admits `true` would let a write of `true`
// reach it: after the write through `wide`, `r.bag` is `true` where
// `null | R` is claimed (TypeScript reads a field covariantly).
interface Bag {
  bag: null | R;
}
interface R extends Bag {
  (x: boolean): boolean;
}

function make(): R {
  return Object.assign<(x: boolean) => boolean, { bag: null | R }>(
    (x: boolean): boolean => x,
    { bag: null },
  );
}

export function wrong(): null | R {
  const r = make();
  const wide: { bag: null | R | boolean } = r;
  wide.bag = true;
  return r.bag;
}
