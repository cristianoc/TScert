// What a test finds of a field declared at a named union of records is the
// union itself: its arms, whose generic methods only their declarations
// state, are never copied into a claim.
interface Each {
  each<T>(f: (s: string) => T): T | undefined;
}
interface One extends Each {
  readonly kind: 1;
}
interface Two extends Each {
  readonly kind: 2;
}
type Spec = One | Two;
interface Holder {
  readonly kind: 3;
  readonly spec?: Spec;
}
type Item = Holder | { readonly kind: 4 };

export function holders(items: Item[], out: Holder[]): void {
  for (const item of items) if (item.kind === 3 && item.spec) out.push(item);
}
