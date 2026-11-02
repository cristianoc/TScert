// A logical expression keeps its numeric zero result on short circuit.
// Node observes a number where the function promises a Boolean.
type Holder = { kind: "array"; items: number[] } | { kind: "other" };
export function wrong(holder: Holder): boolean {
  return (
    holder.kind === "array" &&
    holder.items.length &&
    holder.items.every((value) => value > 0)
  );
}
