// A Map built from a callback's array literals, `new Map(xs.map(x => [k,
// x]))`, holds the pairs' types: the literal is a tuple where the Map's
// binders reach the callback's result, and its values are the elements.
// Census functions:
// declaration-graph.mts#selectGlobal.
type Form = { name: string; binders: string[]; size: number };

export function firstBinders(forms: readonly Form[]): number {
  const distinct = [...new Map(forms.map((f) => [f.name, f])).values()];
  const [only] = distinct;
  if (distinct.length === 1 && only) return only.binders.length;
  return only?.size ?? 0;
}
