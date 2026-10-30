// Successive tests of a field leave facts about what it holds, all of which
// hold: an arm whose field holds none of what they admit is no arm of the
// object. `{ kind: "a" | "b" }` is excluded once `kind` failed both, in a
// switch, in an `if` chain and through an alias of the field's type, and a
// default reached by no arm receives `never`; `{ op: 1 | 2 }` likewise once
// `op` failed `1` and `2`.
type Pair = "a" | "b";
type Kind =
  | { kind: Pair }
  | { kind: "c"; v: string }
  | { kind: "d"; n: number };
function unmatched(x: never): never {
  throw Error(`no kind: ${JSON.stringify(x)}`);
}
export function described(k: Kind): string {
  switch (k.kind) {
    case "a":
      return "a";
    case "b":
      return "b";
    case "c":
      return k.v;
    case "d":
      return `${k.n}`;
    default:
      return unmatched(k);
  }
}
export function chained(k: Kind): string {
  if (k.kind === "a") return "a";
  if (k.kind === "b") return "b";
  if (k.kind === "c") return k.v;
  return `${k.n}`;
}
type Op =
  | { readonly op: 1 | 2; readonly a: string }
  | { readonly op: 1 | 2 | 3; readonly b: number };
export function numbered(o: Op): number {
  if (o.op === 1) return 1;
  if (o.op === 2) return 2;
  return o.b;
}
