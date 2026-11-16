// A bound stated at a field, `cursor.at < flags.length`, kept across a call
// whose stated effect may grow every store: the field holds a number, of
// class `values`, which the effect on `stores` leaves alone, so the bound
// still holds at the read.
type Visitor = (w: number) => Modifies<{ values: "keep"; stores: "grow" }, void>;
type Cursor = { at: number };
/** @requires safeInteger(cursor.at) && 0 <= cursor.at && cursor.at < flags.length */
export function read(flags: Uint8Array, cursor: Cursor, visit: Visitor): number {
  visit(0);
  return flags[cursor.at]!;
}
