type Value =
  | { readonly kind: "text"; readonly text: string }
  | { readonly kind: "empty" };

export function read(holder: { readonly value: Value }): string {
  return holder.value.kind === "text" ? holder.value.text : "";
}

export function split(holder: { readonly value: Value }): string {
  if (holder.value.kind === "text") return holder.value.text;
  return "";
}
