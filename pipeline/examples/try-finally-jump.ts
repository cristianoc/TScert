// A `break` or `continue` leaving a `try` runs its `finally` on the way,
// innermost first, each in its `try`'s context, then lands; a `finally`
// that jumps itself leaves by its own way.
export function breakThroughFinally(xs: number[]): number {
  let count = 0;
  for (const x of xs) {
    try {
      if (x < 0) {
        break;
      }
      count = count + 1;
    } finally {
      count = count * 2;
    }
  }
  return count;
}

export function continueThroughTwo(xs: number[]): number {
  let n = 0;
  for (const x of xs) {
    try {
      try {
        if (x > 0) continue;
        n = n + 1;
      } finally {
        n = n + 2;
      }
    } finally {
      n = n + 3;
    }
  }
  return n;
}

export function switchThroughFinally(k: number): "a" | "b" {
  let x: "a" | "b" = "a";
  switch (k) {
    case 1:
      try {
        break;
      } finally {
        x = "b";
      }
    default:
      x = "a";
  }
  return x;
}

export function exitState(n: number): "b" {
  let x: "a" | "b" = "a";
  let i = 0;
  while (i < n) {
    i = i + 1;
    try {
      x = "a";
      break;
    } finally {
      x = "b";
    }
  }
  if (x === "a") return "b";
  return x;
}

export function jumpFromCatch(c: () => boolean, mayThrow: () => void): number {
  let n = 0;
  while (c()) {
    try {
      mayThrow();
    } catch {
      break;
    } finally {
      n = 1;
    }
  }
  return n;
}

export function finallyOverridesJump(c: () => boolean): number {
  while (c()) {
    try {
      break;
    } finally {
      return 1;
    }
  }
  return 0;
}
