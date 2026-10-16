// A condition that may be false takes either arm. `ready` is captured and
// reset before `pick` runs, so `ready || zs[0]` reads the element, and on an
// empty array it is `undefined` where `true` is claimed (TypeScript reads an
// element at the array's element type).
export function stale(ys: true[]): true {
  let ready = true;
  const reset = (): void => {
    ready = false;
  };
  const pick = (zs: true[]): true => ready || zs[0];
  reset();
  return pick(ys);
}
