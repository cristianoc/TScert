// A non-empty string (`s !== ""`, `if (s)`, or non-empty string literal types)
// has UTF-16 length at least 1, and an empty string (`s === ""` or `if (!s)`)
// has length 0.

/** @requires safeInteger(n) && 1 <= n */
function requirePositive(n: number): number {
  return n;
}

/** @requires safeInteger(n) && n === 0 */
function requireZero(n: number): number {
  return n;
}

/** @requires safeInteger(n) && n === 3 */
function requireThree(n: number): number {
  return n;
}

export function fromNotEmpty(s: string): number {
  if (s !== "") {
    const n = s.length;
    return requirePositive(n) + s.codePointAt(0)!;
  }
  return 0;
}

export function fromTruthy(s: string): number {
  if (s) {
    const n = s.length;
    return requirePositive(n) + s.codePointAt(0)!;
  }
  return requireZero(s.length);
}

export function fromEmptyBranch(s: string): number {
  if (s === "") {
    return requireZero(s.length);
  }
  const n = s.length;
  return requirePositive(n) + s.codePointAt(0)!;
}

export function lengthBeforeCheck(s: string): number {
  const n = s.length;
  if (s !== "") {
    return requirePositive(n);
  }
  return requireZero(n);
}

export function lengthBeforeTruthy(s: string): number {
  const n = s.length;
  if (s) {
    return requirePositive(n);
  }
  return requireZero(n);
}

export function fromNonEmptyLiterals(s: "alpha" | "beta"): number {
  return requirePositive(s.length) + s.codePointAt(0)!;
}

export function fromLiteral(s: "abc"): number {
  return requireThree(s.length);
}

function missing(): never {
  throw new RangeError("missing");
}

export function fromOptionalNotEmpty(s: string | undefined): number {
  if (s !== "") {
    const t = s ?? missing();
    const n = t.length;
    return requirePositive(n) + t.codePointAt(0)!;
  }
  return 0;
}

export function fromOptionalTruthy(s: string | undefined): number {
  if (s) {
    const n = s.length;
    return requirePositive(n);
  }
  return 0;
}
