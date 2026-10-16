// A nested `switch` whose cases cover its scrutinee's type and all return
// leaves no path out of the clause: past it the scrutinee would be of the
// empty type, so the point after the outer `switch` is reached from `case 0`
// alone, where `v` holds a string.
export function f(x: 0 | 1, y: 0 | 1): string {
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
  return v.toUpperCase();
}
