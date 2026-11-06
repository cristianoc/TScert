// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): prepare.ts#measureAnalysis.
// Refusal: reject: source expression obligation: no derivation of its
// return-contract claim, a record literal `{ widths, segments }` returned at
// a union of two records whose arms state an optional `items` it leaves out.
// A record literal expected at a union of records, no written field of which
// selects one arm, is claimed with its exact keys when an arm states an
// optional field it leaves out: the literal is fresh, so it owns no other
// key, and that bound is what lets it meet the arm.
type Data = { widths: number[]; items?: never }

export function measure(keep: boolean): (Data & { segments: string[] }) | (Data & { segments?: never }) {
  const widths: number[] = [1, 2]
  const segments = keep ? ["a", "b"] : null
  if (segments !== null) return { widths, segments }
  return { widths }
}

export function total(keep: boolean): number {
  const data = measure(keep)
  return data.segments === undefined ? data.widths.length : data.widths.length + data.segments.length
}
