// An imported constant initialized by an array literal naming nothing states
// its type by that literal: the array TypeScript infers, `T[]` with `T` the
// union of its elements' widened types, an element a record or an array in
// turn. The array is writable and read as an annotation `T[]` reads.
import { mixed, offsets, points, rows } from "@fixture/lib";

export function first(): number {
  return offsets.length + (offsets[0] ?? 0);
}

export function labelled(): string {
  const p = points[1];
  return p === undefined ? "" : p.label + p.x;
}

export function cell(): number {
  return rows[1]?.[1] ?? 0;
}

export function kinds(): string | number | null {
  return mixed[2] ?? null;
}

export function appended(): number {
  offsets.push(3);
  return offsets.length;
}
