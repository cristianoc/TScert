type Value = { kind: "text"; text: string } | { kind: "empty" };

export function wrong(
  first: { value: Value },
  second: { value: Value },
): string {
  let holder = first;
  const replace = (): void => {
    holder = second;
  };
  if (holder.value.kind === "text") {
    replace();
    return holder.value.text;
  }
  return "";
}
