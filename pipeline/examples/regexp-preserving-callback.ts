// Callbacks calling a string's methods with a regex: a non-global,
// non-sticky native regex's members write nothing, `[Symbol.search]`
// restores the `lastIndex` it saved and `[Symbol.split]` steps a fresh clone,
// so each call states heap preservation, through `%Dispatch:m%`'s signature
// at a target whose member states it, and `map`'s result is dense.
export function firstFields(lines: string[]): string[] {
  return lines.map((l) => l.trim().split(/\s{3,}/)[0] ?? "");
}

export function unquoted(lines: string[]): string[] {
  return lines.map((l) => l.replace(/^"|"$/, "").replace(/^'/, ""));
}

export function marks(lines: string[]): boolean[] {
  const word = /^\w+$/;
  return lines.map((l) => word.test(l) || /^-?\d+$/.test(l));
}

// A global regex's search and split leave its `lastIndex` as they found it.
export function positions(lines: string[]): number[] {
  const digit = /\d/g;
  return lines.map((l) => l.search(digit) + l.split(digit).length);
}
