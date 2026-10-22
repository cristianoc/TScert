// A recursive constant storing its self entry in a holder whose method
// takes a wider parameter and one more: a method's parameters are compared
// both ways, so TypeScript admits it, and a later call through the holder
// passes the closure a value outside its parameter, whose `k` it returns as
// its string.
type Term = { readonly k: string; readonly parts: readonly Term[] };
type Loose = { readonly k: unknown; readonly parts: readonly Term[] };
interface Later {
  run(u: Loose, depth: number): string;
}

export function wrong(t: Term, odd: Loose): string {
  const held: Later[] = [];
  const show = (u: Term): string => {
    held.push({ run: show });
    return u.k;
  };
  show(t);
  for (const h of held) return h.run(odd, 1);
  return "";
}
