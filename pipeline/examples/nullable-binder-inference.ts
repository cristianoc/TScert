// A binder in a union with ground atoms, `A | null`, is inferred from what
// the actual holds beside them, inline or through an alias, as a parameter
// and as a construct signature's instance.
type Maybe<T> = T | null;
declare function unwrapInline<A>(value: A | null): A;
declare function unwrapAlias<A>(value: Maybe<A>): A;
declare function unbox<A>(ctor: { new (): A | null }): A;
declare const sn: string | null;
declare const CtorSN: { new (): string | null };

export function direct(): string {
  const ok = unwrapInline(sn);
  const viaAlias = unwrapAlias(sn);
  return ok + viaAlias;
}

// The alias on the argument's side: its atoms are its declaration's.
declare const sm: Maybe<string>;
export function aliasArgument(): string {
  const s = unwrapInline(sm);
  return s;
}

export function constructed(): string {
  return unbox(CtorSN);
}
