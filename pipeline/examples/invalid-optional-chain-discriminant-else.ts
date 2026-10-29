// Where `found?.ok` is falsy, `found` may be nullish: the chain's failure
// says nothing of the receiver.
type Answered = { readonly ok: true; readonly value: number } | { readonly ok: false; readonly refused: string };

export function wrong(found: Answered | undefined): { readonly ok: false; readonly refused: string } | null {
  return found?.ok ? null : found;
}
