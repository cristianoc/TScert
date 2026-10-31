// Census function: declaration-graph.mts#selectGlobal.
// The allocation states its writable contract. JSON serialization also
// needs a bound on the nested records' additional keys and hooks.
type Term = { k: "a"; span: number } | { k: "b"; span: number; value: string };
type Form = { type: Term; binders: string[] };
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
