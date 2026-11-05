// `do...while`: the body runs before the test, a `continue` goes to the
// test, a `break` leaves the loop without it, and the body's bindings are
// out of the test's scope.

// A varint as pretext's `unpackTable` reads one: the binding the body
// assigns is read by the test.
export function varint(input: string, start: number): number {
  let at = start;
  let value = 0;
  let scale = 1;
  let byte: number;
  do {
    byte = input.charCodeAt(at++);
    value += (byte & 0x7f) * scale;
    scale *= 0x80;
  } while (byte >= 0x80);
  return value;
}

// The body runs once under a false test.
export function once(): number {
  let runs = 0;
  do runs++;
  while (false);
  return runs;
}

// A `continue` runs the test once; a `break` in a `switch` leaves the
// `switch`, one after it the loop.
export function tests(codes: number[]): number {
  let i = 0;
  let tested = 0;
  do {
    switch (codes[i]) {
      case 32:
        i++;
        continue;
      case 9:
        i++;
        break;
      default:
        return tested;
    }
    if (i > 8) break;
  } while ((tested++, i < codes.length));
  return tested;
}

// A `finally` replacing a `continue` with a `break`.
export function replaced(limit: number): number {
  let k = 0;
  do {
    try {
      k++;
      continue;
    } finally {
      if (k >= limit) break;
    }
  } while (k < 10);
  return k;
}

// The body's `const` shadows the outer one; the test reads the outer.
export function shadowed(n: number): string {
  const x = n;
  let out = "";
  do {
    const x = "s";
    out += x;
  } while (out.length < x);
  return out;
}

// The first run of the body sees the entry's `x`, of either type: only
// the runs after a test see it narrowed to a string.
export function lengthOf(x: string | number): number {
  let total = 0;
  do {
    total += typeof x === "string" ? x.length : 1;
  } while (typeof x === "string" && total < 10);
  return total;
}
