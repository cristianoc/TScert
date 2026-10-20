type Value = { kind: "text"; text: string } | { kind: "empty" };

export function wrong(
  holder: { value: Value },
  alias: { value: Value },
): string {
  if (holder.value.kind === "text") {
    alias.value = { kind: "empty" };
    return holder.value.text;
  }
  return "";
}
