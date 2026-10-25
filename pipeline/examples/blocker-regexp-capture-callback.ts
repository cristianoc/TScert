// A replacement callback needs the regex capture arguments admitted by its
// callable contract.
// Census functions:
// regexp-shape.mts#decodeName, regexp-shape.mts#groupsOf,
// regexp-shape.mts#regexpShape.
export function use(raw: string): string {
  return raw.replace(/(a)|(b)/g, (_: string, a: unknown, b: unknown) =>
    typeof a === "string" ? a : typeof b === "string" ? b : "",
  );
}
