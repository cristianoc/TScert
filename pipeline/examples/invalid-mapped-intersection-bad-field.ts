// A non-BaseItem field violates the mapped-type part of the intersection bound
// directly in Lean.
declare const itemBrand: unique symbol;

declare abstract class BaseItem {
  readonly [itemBrand]: never;
}

type TaggedItems<T> = {
  readonly [K in keyof T]: BaseItem;
} & {
  readonly extra?: BaseItem;
};

declare function acceptTagged<T extends TaggedItems<T>>(items: T): number;

export function rejectBadField(): number {
  return acceptTagged<{ readonly first: number }>({ first: 42 });
}
