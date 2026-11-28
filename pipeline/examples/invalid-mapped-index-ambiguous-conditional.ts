// Soundness: a mapped-index conditional checking an unbranded interface
// against a structurally overlapping record without nominal inheritance is
// refused at source instead of trusting TypeScript's structural check.
interface UnbrandedBase {
  readonly tag: string;
}

type MatchingKeys<T> = {
  [K in keyof T & string]: T[K] extends UnbrandedBase ? K : never;
}[keyof T & string];

declare function pickKey<T, const K extends MatchingKeys<T>>(obj: T, key: K): K;

type StructuralOverlap = {
  readonly item: { readonly tag: string };
};

export function rejectAmbiguous(s: StructuralOverlap): "item" {
  return pickKey(s, "item");
}
