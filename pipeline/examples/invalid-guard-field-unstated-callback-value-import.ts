// A guard on a field holding an array beside null or a number, a `forEach`
// whose callback calls an imported function of a module the gate refuses
// (lib.ts holds a module-level `let`), then the field's reread. The import
// is read at its declaration, which states no effect, so the callback may
// change the field and the call keeps nothing the guard found. Stands for
// the census function diagnostic.mts#readDiagnostic
// (`claim.context.forEach(labels)` after `available.forEach(labels)`,
// `labels` calling type-graph.mts's `decodeLabels`).
import { double } from "@fixture/lib";

type Value = null | number | readonly Value[];
type Row = { readonly context: Value };
export function count(t: Row, seen: Value, size: number): number {
  const labels = (v: Value) => double(size);
  if (!Array.isArray(seen) || !Array.isArray(t.context)) return 0;
  seen.forEach(labels);
  t.context.forEach(labels);
  return t.context.length;
}
