// A nested `switch` that does not cover `2` leaves a path out of the clause
// with `v` holding 42: it is no string.
export function f(x: 0 | 1, y: 0 | 1 | 2): string {
  let v: string | number = "init";
  switch (x) {
    case 0:
      v = "a";
      break;
    case 1:
      v = 42;
      switch (y) {
        case 0:
          return "r0";
        case 1:
          return "r1";
      }
  }
  return v as string;
}
