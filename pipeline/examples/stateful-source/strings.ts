/**
 * Strings in the source fragment. Like numbers they are opaque: bound, passed,
 * stored in a union, shape-tested and compared with a literal, never computed
 * with. A literal is its own singleton, below the family.
 */
function idString(x: string): string {
  return x;
}

/** A literal result is its singleton, and the singleton is below the family. */
function literalResult(): string {
  return "ready";
}

/** An annotated copy keeps the annotation, exactly as a Boolean copy does. */
function copyString(x: string): string {
  const y: string = x;
  return y;
}

/** A singleton type is preserved end to end, not widened to the family. */
function singletonString(x: "on"): "on" {
  return x;
}

/** Nullable strings refine like any other union member. */
function guardString(x: string | null): string {
  if (x !== null) {
    return x;
  }
  return "";
}

/** Equality with a literal decides a finite union: what is not "a" is "b". */
function discriminate(kind: "a" | "b"): "b" {
  if (kind === "a") return "b";
  return kind;
}
