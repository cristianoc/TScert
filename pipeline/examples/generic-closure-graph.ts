// A generic closure is graph code at a scheme row: its body takes any
// statement form, and its code is checked once, at the scheme's signature.
function statements(flag: boolean, count: number): number {
  const pick = <T, U>(first: T, second: U, useFirst: boolean): T | U => {
    let chosen: T | U = second;
    if (useFirst) {
      chosen = first;
    }
    return chosen;
  };
  const a = pick(flag, count, flag);
  return typeof a === "number" ? a : count;
}

// A bounded binder is read as the meet of its row and its bound.
function bounded(n: number): number {
  const size = <T extends { length: number }>(value: T): number => value.length;
  return size({ length: n, name: "x" });
}

// A generic closure inside a generic body: its binders are its scheme's,
// apart from the body's.
function nested<T>(value: T): T {
  const second = <U>(first: U, last: T): T => last;
  return second(0, value);
}

// A generic closure no call instantiates is still checked at its scheme.
function unused(): void {
  const f = <T extends string>(x: T): T => x;
  void f;
}
