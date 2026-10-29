// A global the file only declares may be an accessor of the global object,
// which answers each read anew: the chain's truthiness says nothing of a
// later read of it.
type Answered = { readonly ok: true; readonly value: number } | { readonly ok: false; readonly refused: string };
declare const current: Answered | undefined;

export function wrong(): number {
  return current?.ok ? current.value : 0;
}
