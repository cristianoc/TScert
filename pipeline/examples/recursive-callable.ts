// A function whose field holds either null or a function of its own type:
// `R` is recursive through the function's bag. The bag can hold the function
// itself, and what is read back is called at `R`'s signature.
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

export function selfLoop(): boolean {
  const r = make();
  r.bag = r;
  const inner = r.bag;
  return inner === null ? true : inner(false);
}

// A recursive function is passed and returned at `R`.
export function pass(f: R): R {
  return f;
}
export function passed(): R {
  return pass(make());
}
