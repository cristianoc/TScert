// Callers whose written instance is checked against the callback they pass
// (the argument's type at rule Inst of "An effect language for TScert"):
// the callback's effect, read from its body, is included in the instance.
// The walker is W1's (w1.ts). Negative callers say whether the program is
// unsafe or only unprovable.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };

export function walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]!, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

function bump(c: { n: number }): Modifies<{ "c.n": "scalar" }, void> {
  c.n++;
}

function note(w: number): void {
  if (w < 0) return;
}

// Positive: the claim is true, a push onto a fresh list.
export function trueClaim(p: Prepared): number {
  const out: number[] = [];
  return walkLines<{ "out[*]": "extend" }>(p, (w) => { out.push(w); });
}

// Negative, only unprovable: the claim says a fresh list, the callback grows
// the walked array (the loop runs until push throws at the maximal length).
export function falseClaim(p: Prepared): number {
  const out: number[] = [];
  return walkLines<{ "out[*]": "extend" }>(p, () => { p.widths.push(0); });
}

// Negative, only unprovable (both writes are to fresh storage, so the program
// is safe): the callback writes two captures, the claim names one.
export function omittedWrite(p: Prepared): number {
  const out: number[] = [];
  const seen = { n: 0 };
  return walkLines<{ "out[*]": "extend" }>(p, (w) => { out.push(w); seen.n++; });
}

// Negative, only unprovable: the callback calls a function whose effect is
// not stated, so its effect cannot be bounded.
export function unknownHelper(p: Prepared): number {
  return walkLines<{}>(p, (w) => { note(w); });
}

// Positive: the callback calls a function whose stated effect, at its
// argument, is within the claim.
export function statedHelper(p: Prepared): number {
  const seen = { n: 0 };
  return walkLines<{ "seen.n": "scalar" }>(p, () => { bump(seen); });
}

// Positive: the callback pushes through a `const` alias of a capture; the
// alias holds the capture's path, so the claim on `lines` covers it.
export function aliasCapture(p: Prepared): number {
  const lines: number[] = [];
  const l = lines;
  return walkLines<{ "lines[*]": "extend" }>(p, (w) => { l.push(w); });
}

// Negative, only unprovable: the inner `out` shadows the fresh list and holds
// the walked array; the claim on `out` resolves to it.
export function shadowed(p: Prepared): number {
  const out: number[] = [];
  out.push(0);
  {
    const out = p.widths;
    return walkLines<{ "out[*]": "extend" }>(p, (w) => { out.push(w); });
  }
}
