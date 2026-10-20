type Value = { kind: "text"; text: string } | { kind: "empty" };

export function wrong(
  first: { value: Value },
  second: { value: Value },
): string {
  let holder = first;
  if (holder.value.kind === "text") {
    holder = second;
    return holder.value.text;
  }
  return "";
}
