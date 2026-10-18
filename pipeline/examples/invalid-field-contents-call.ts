// A call between two tests of a field may write it: what the first test
// found is no fact after the call, so the second test alone excludes no arm.
// `setA` writes "a" into a `{ kind: "a" | "b" }` object that failed the test
// for "a".
type Kind = { kind: "a" | "b" } | { kind: "c"; v: string };
function setA(k: Kind): void {
  if (k.kind !== "c") k.kind = "a";
}
export function wrong(k: Kind): string {
  if (k.kind === "a") return "";
  setA(k);
  if (k.kind === "b") return "";
  return k.v;
}
