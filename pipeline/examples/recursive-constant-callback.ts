// A recursive constant passing its own name as a callback in its body: the
// read is the closure's self entry, which holds the closure at its whole
// claim, so the closure is offered the callback's longer signature there as
// where any other read passes it, and its code is checked at that signature
// with the self entry at the claim. Module-level and local, annotated
// directly and through an alias, in a nested callback after a union test,
// bound under an annotation of a longer signature that a later call passes
// more arguments, read by a default and through a bound wrapper, and at a
// variadic signature whose fixed parameters cover the closure's.
type Term =
  | { readonly k: "binder"; readonly name: string }
  | { readonly k: "union"; readonly parts: readonly Term[] }
  | { readonly k: "atom"; readonly name: string };

const binder = (t: Term): boolean =>
  t.k === "binder" || (t.k === "union" && t.parts.some(binder));

export function hasBinder(t: Term): boolean {
  return binder(t);
}

export function anyBinder(terms: readonly Term[]): boolean {
  return terms.some((part) => {
    if (part.k !== "union") return false;
    const local = (t: Term): boolean =>
      t.k === "binder" || (t.k === "union" && t.parts.every(local));
    return local(part);
  });
}

export function annotated(t: Term): boolean {
  const open: (t: Term) => boolean = (u) =>
    u.k !== "union" || u.parts.some(open);
  return open(t);
}

type Test = (t: Term) => boolean;

export function aliased(t: Term): boolean {
  const open: Test = (u) => u.k !== "union" || u.parts.every(open);
  return open(t);
}

type Step = (t: Term, depth: number) => string;

export function escaped(t: Term): string {
  const show = (u: Term): string => {
    const later: Step = show;
    if (u.k !== "union") return u.k;
    let out = "";
    for (const part of u.parts) out += later(part, 1);
    return out;
  };
  return show(t);
}

type Row = (n: number, d: number | undefined, extra: string) => number;

export function defaultsAndBind(): number {
  const f = (n: number, d: number = n > 0 ? f(0) : 0): number => {
    const again: Row = f;
    return n <= 0 ? d : again(n - 1, undefined, "ignored");
  };
  const bound = f.bind(null, 2);
  return bound();
}

type Rest = (n: number, ...extra: string[]) => number;

export function variadic(): number {
  const f = (n: number): number => {
    const again: Rest = f;
    return n <= 0 ? 0 : again(n - 1, "ignored", "also ignored");
  };
  return f(2);
}
