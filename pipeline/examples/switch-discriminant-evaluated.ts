// A `switch` evaluates its discriminant before any clause, also when no
// `case` test would read it again: a `typeof` of a name before its
// initialization, or the name itself, throws there, and the handler answers
// 1 (run under Node). A `case` test reads the discriminant first, so a
// switch with one throws at the same point.
export function defaultOnly(): number {
  try {
    switch (typeof x) {
      default:
        return 0;
    }
  } catch {
    return 1;
  }
  let x: number = 0;
  return x;
}

export function empty(): number {
  try {
    switch (y) {
    }
  } catch {
    return 1;
  }
  let y: number = 0;
  return y;
}

export function tested(): number {
  try {
    switch (typeof z) {
      case "number":
        return 0;
      default:
        return 2;
    }
  } catch {
    return 1;
  }
  let z: number = 0;
  return z;
}
