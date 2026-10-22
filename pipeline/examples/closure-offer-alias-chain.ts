// A named closure over a chain of union aliases sharing their operands,
// passed to `forEach` over an array of an earlier alias: offered the
// callback's signature at that element.
type T0 = { k: "a" };
type T1 = { k: "b" };
type T2 = T1 | T0;
type T3 = T2 | T1;
type T4 = T3 | T2;
type T5 = T4 | T3;
type T6 = T5 | T4;
type T7 = T6 | T5;
type T8 = T7 | T6;
type T9 = T8 | T7;
type T10 = T9 | T8;
type T11 = T10 | T9;
type T12 = T11 | T10;
type T13 = T12 | T11;
type T14 = T13 | T12;

export function each(xs: T12[]): void {
  const go = (value: T14): void => {};
  xs.forEach(go);
}
