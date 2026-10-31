// Census function: declaration-graph.mts#selectGlobal.
// A map callback replaces a nested field while retaining the outer record.
type Term = { k: "a"; span: number } | { k: "b"; span: number; value: string };
type Form = { type: Term; binders: string[] };
export function keys(given: Form[], inputs: string[]): Form[] {
  const forms = [
    ...given,
    ...inputs.map((value) => ({
      binders: [],
      type: { k: "b", span: 0, value } satisfies Term,
    })),
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
