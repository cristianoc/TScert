// Computed alias whose body is an intersection of a homomorphic mapped type
// with a record (including an optional `never` symbol property).
declare const itemBrand: unique symbol;

declare abstract class BaseItem {
  readonly [itemBrand]: never;
}

interface SubItem extends BaseItem {
  readonly label: string;
}

type AllItems<T> = {
  readonly [K in keyof T]: BaseItem;
} & {
  readonly [Symbol.iterator]?: never;
};

type TaggedItems<T> = {
  readonly [K in keyof T]: BaseItem;
} & {
  readonly extra?: BaseItem;
};

declare function acceptItems<T extends AllItems<T>>(items: T): number;
declare function acceptTagged<T extends TaggedItems<T>>(items: T): number;

type MarkedItems = {
  readonly first: SubItem;
  readonly [Symbol.iterator]?: never;
};

export function useMappedIntersections(
  marked: MarkedItems,
  item: SubItem,
): number {
  const a = acceptItems(marked);
  const b = acceptTagged({ first: item, extra: item });
  return a + b;
}
