type Value = { kind: "text"; text: string } | { kind: "empty" };

export function wrong(holder: { value: Value }, replace: () => void): string {
  if (holder.value.kind === "text") {
    replace();
    return holder.value.text;
  }
  return "";
}
