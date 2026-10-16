// A parameter hiding a module constant of its name: a jump carries each
// binding by its own identity, so a test narrowing the parameter leaves the
// constant's slot as it is.
const b: number = 1;

export function sometimes(b: boolean): number {
  if (b) {
    throw new Error("maybe");
  }
  return 2;
}

export function narrowed(b: boolean): false {
  if (b) {
    throw new Error("maybe");
  }
  return b;
}

export function outer(): number {
  return b;
}
