// A `let` or an assigned parameter that every closure mentioning it sees at
// its value when the closure was created is a slot of its activation: what a
// write put there survives a call, a throw and a later closure run.

type List<T> = null | { head: T; tail: List<T> };

// A call cannot reach the slot: `y` is still "a" where the call throws.
export function survivesCall(a: "a", b: "b", mayThrow: () => void): "a" {
  let y: "a" | "b" = a;
  y = b;
  y = a;
  try {
    mayThrow();
  } catch {
    return y;
  }
  return y;
}

// An inner try whose catch only writes the slot absorbs every throw: the
// outer catch is entered from the second call alone, with `y` at "a".
export function absorbedInnerTry(a: "a", b: "b", mayThrow: () => void): "a" {
  let y: "a" | "b" = a;
  try {
    try {
      y = b;
      mayThrow();
      y = a;
    } catch {
      y = a;
    }
    mayThrow();
  } catch {
    return y;
  }
  return y;
}

// The closure is created after the last write: it captures the value.
export function capturedAfterWrites(tag: boolean): () => string {
  let x: string;
  if (tag) {
    x = "yes";
  } else {
    x = "no";
  }
  return () => x;
}

// A test narrows an assigned parameter holding an object or null.
export function reverse(l: List<number>): List<number> {
  let result: List<number> = null;
  while (l !== null) {
    result = { head: l.head, tail: result };
    l = l.tail;
  }
  return result;
}
