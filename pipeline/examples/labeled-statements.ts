// Labeled statements: a `break ℓ` leaves the statement labeled `ℓ`, through
// nested loops, a `switch` and a `finally`; a `continue ℓ` goes on with the
// loop labeled `ℓ` from a nested loop, running its update.

// A labeled block left early, as pretext's line walker leaves `decided`.
export function decide(widths: number[], limit: number): number {
  let end = -1;
  decided: {
    let i = 0;
    for (const w of widths) {
      if (w > limit) {
        end = i;
        break decided;
      }
      i++;
    }
    end = widths.length;
  }
  return end;
}

// A `continue` of the outer loop from the inner one runs the outer update.
export function rowsWithout(row: number[], banned: number[]): number {
  let kept = 0;
  let r = 0;
  outer: for (; r < banned.length; r++) {
    for (const v of row) if (banned.includes(v)) continue outer;
    kept++;
  }
  return kept * 100 + r;
}

// The kind after the loop is the last row's: a string where a `continue`
// of the outer loop skipped the assignment after the inner one.
export function lastKind(rows: number[][]): string | number {
  let kind: string | number = 0;
  let r = 0;
  outer: for (const row of rows) {
    r++;
    for (const v of row) {
      if (v < 0) {
        kind = "skipped";
        continue outer;
      }
    }
    kind = r;
  }
  return kind;
}

// A loop with a binding per iteration, which a closure captures, continued
// from a nested loop: each closure sees its own iteration's `i`.
export function captured(row: number[], n: number): number {
  const reads: (() => number)[] = [];
  outer: for (let i = 0; i < n; i++) {
    for (const v of row) if (v === i) continue outer;
    reads.push(() => i);
  }
  let sum = 0;
  for (const read of reads) sum += read();
  return sum;
}

// Two labels on one loop; a `break` of a `switch` inside it, and a `break`
// of the outer label from the `switch`.
export function chained(codes: number[]): number {
  let seen = 0;
  a: b: for (const c of codes) {
    switch (c) {
      case 0:
        continue a;
      case 1:
        break;
      case 2:
        break b;
    }
    seen++;
  }
  return seen;
}

// A `finally` between the jump and its label runs on the way out, and one
// replacing the jump replaces it.
export function finals(rows: number[][]): string {
  let log = "";
  outer: for (const row of rows) {
    try {
      for (const v of row) {
        if (v === 1) continue outer;
        if (v === 2) break outer;
      }
    } finally {
      log += "f";
    }
    log += "r";
  }
  return log;
}
