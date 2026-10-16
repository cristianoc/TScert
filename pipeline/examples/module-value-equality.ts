// A comparison with a module value's field, an enum member or an ambient
// constant's, narrows the other operand as one with a local's does.
enum E {
  A,
  B,
}
declare const globalObj: { v: 1 | 2 };

export function member(x: E): 1 {
  if (x === E.A) {
    return 1;
  }
  return x;
}

export function field(x: 0 | 1 | 2): 1 | 2 | 3 {
  if (x === globalObj.v) {
    return x;
  }
  return 3;
}
