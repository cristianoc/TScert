// A spread of a string copies its code units at its indices; of a class
// value, its static fields. The copy of a `{}` states none of those keys, and
// a field written after the spread is the copy's: `{}` admits a string and a
// class value.
export function afterSpread(): { a: string } {
  const obj: {} = { a: 1 };
  return { ...obj, a: "" };
}

class C {
  static readonly x: number = 1;
}
export function afterClass(): { b: number } {
  return { ...C, b: 2 };
}
