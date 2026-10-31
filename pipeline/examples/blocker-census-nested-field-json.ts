// Census function: declaration-graph.mts#selectGlobal.
// Term and form annotations retain the JSON data bound of their constructors.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
type Data = { readonly [key: string]: Json };
type Term =
  | { k: "a"; span: number; parts: Term[] }
  | { k: "b"; span: number; value: string };
type Form = {
  readonly [key: string]: Json;
  type: Term & Data;
  binders: string[];
};
export function keys(given: Form[], inputs: string[]): Form[] {
  const forms = [
    ...given,
    ...inputs.map((value): Form => {
      const type: Extract<Term, { k: "b" }> & Data = { k: "b", span: 0, value };
      return { binders: [], type };
    }),
  ];
  const distinct = [
    ...new Map(
      forms.map((f): [string, Form] => {
        const data: Data = f.type;
        return [JSON.stringify({ ...f, type: { ...data, span: null } }), f];
      }),
    ).values(),
  ];
  return distinct;
}
