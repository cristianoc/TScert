// Soundness: an open record `{ readonly first: SubItem }` does not rule out an
// extra `[Symbol.iterator]` property, so Lean soundly rejects it against
// `{ readonly [K in keyof T]: BaseItem } & { readonly [Symbol.iterator]?: never }`.
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

declare function acceptItems<T extends AllItems<T>>(items: T): number;

type OpenItems = {
  readonly first: SubItem;
};

export function rejectOpen(open: OpenItems): number {
  return acceptItems(open);
}
