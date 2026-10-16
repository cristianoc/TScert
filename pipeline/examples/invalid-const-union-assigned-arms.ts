// A `let` that is written keeps its declared union: the write may put the
// other arm there, whose writable `value: number` is no `value: unknown`.
type Option<T> = { kind: "some"; value: T } | { kind: "none" };

function isNone(
  option: { kind: "some"; value: unknown } | { kind: "none" },
): boolean {
  return option.kind === "none";
}

export function use(flag: boolean): boolean {
  let option: Option<number> = { kind: "none" };
  if (flag) {
    option = { kind: "some", value: 1 };
  }
  return isNone(option);
}
