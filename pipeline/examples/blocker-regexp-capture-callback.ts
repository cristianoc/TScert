// A replacement callback taking the regex's captures as `unknown` is claimed
// at the callback `[Symbol.replace]` calls.
// Census functions:
// regexp-shape.mts#decodeName, regexp-shape.mts#groupsOf,
// regexp-shape.mts#regexpShape.
export function use(raw: string): string {
  return raw.replace(/(a)|(b)/g, (_: string, a: unknown, b: unknown) =>
    typeof a === "string" ? a : typeof b === "string" ? b : "",
  );
}
