// Census function: declaration-graph.mts#selectGlobal.
// Construct forms are JSON data. Fresh mapped records state their full
// writable contracts before serialization and deduplication.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
type Term =
  | { readonly [key: string]: Json; k: "a"; span: number }
  | { readonly [key: string]: Json; k: "b"; span: number; value: string };
type Form = { readonly [key: string]: Json; type: Term; binders: string[] };
export function keys(given: Form[], inputs: string[]): Form[] {
  const forms = [
    ...given,
    ...inputs.map(
      (value): Form => ({
        binders: [],
        type: { k: "b", span: 0, value },
      }),
    ),
  ];
  const distinct = [
    ...new Map(
      forms.map((f) => [
        JSON.stringify({ ...f, type: { ...f.type, span: null } }),
        f,
      ]),
    ).values(),
  ];
  return distinct;
}
