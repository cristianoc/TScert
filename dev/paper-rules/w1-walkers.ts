// Walkers the prototype must refuse in their own body: their bound is weaker
// than what they rely on across the visit.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };

// Negative, unsafe: the bound lets a visitor grow `widths` alone, which
// breaks the equal lengths the read of `flags` relies on.
/** @requires widths.length === flags.length */
export function walkPair<E extends AtMost<{ "widths[*]": "grow"; "flags[*]": "grow"; else: "any" }>>(
  widths: number[], flags: number[], onLine: LineVisitor<E>): number {
  const cursor = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(cursor.i) && 0 <= cursor.i */
  while (cursor.i < widths.length) {
    onLine(0, cursor.i, cursor.i + 1);
    total += flags[cursor.i]!;
    cursor.i = cursor.i + 1;
  }
  return total;
}

// Negative, unsafe: the bound keeps only the field `flags`, and the walker
// reads `prepared.widths` after the visit, which a visitor the bound allows
// may replace by a shorter array.
export function walkField<E extends AtMost<{ "prepared.flags": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(cursor.i) && 0 <= cursor.i */
  while (cursor.i < prepared.widths.length) {
    onLine(0, cursor.i, cursor.i + 1);
    total += prepared.widths[cursor.i]!;
    cursor.i = cursor.i + 1;
  }
  return total;
}

// Positive control: the same walker with the bound keeping the reach.
export function walkReach<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor = { i: 0 };
  let total = 0;
  /** @invariant safeInteger(cursor.i) && 0 <= cursor.i */
  while (cursor.i < prepared.widths.length) {
    onLine(0, cursor.i, cursor.i + 1);
    total += prepared.widths[cursor.i]!;
    cursor.i = cursor.i + 1;
  }
  return total;
}
