// A declaration extending the native `Promise`, returned as one: it holds
// the native contract, its prototype's tag included. The forged controls
// (`pipeline/test.mts`) give it the native members at `number` directly:
// without the tag on its prototype the return is refused; with the tag, on
// it or on a base, the document is, as a tagged prototype no native one.
interface Fake extends Promise<number> {}

export function held(f: Fake): Promise<number> {
  return f;
}
