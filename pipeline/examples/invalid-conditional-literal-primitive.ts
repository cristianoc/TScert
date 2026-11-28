// Rule conditional-literal: `undefined extends void`, so `Ex<"a" | undefined, void>` is `"a"`.
type Ex<T, U> = T extends U ? never : T;

export function voidAbsorbsUndefined(): Ex<"a" | undefined, void> {
  // @ts-expect-error Type 'undefined' is not assignable to type '"a"'
  return undefined;
}
