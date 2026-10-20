type Value = { kind: "text"; text: string } | { kind: "empty" };

export function wrong(): string {
  let reads = 0;
  const holder = {
    get value(): Value {
      reads = reads + 1;
      return reads === 1 ? { kind: "text", text: "ok" } : { kind: "empty" };
    },
  };
  return holder.value.kind === "text" ? holder.value.text : "";
}
