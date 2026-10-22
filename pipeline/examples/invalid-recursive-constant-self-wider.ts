// A recursive constant calling its self entry through a binding whose
// method takes a wider parameter: TypeScript compares a method's
// parameters both ways, and the call passes the closure a value outside its
// parameter, whose `k` it returns as its string.
type Term = { readonly k: string; readonly parts: readonly Term[] };
type Loose = { readonly k: unknown; readonly parts: readonly Term[] };
interface Walker {
  step(u: Loose): string;
}

export function wrong(t: Term, odd: Loose): string {
  const show = (u: Term): string => {
    if (u.parts.length > 0) return u.k;
    const w: Walker = { step: show };
    return w.step(odd);
  };
  return show(t);
}
