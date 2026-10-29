// A replacement callback a native regex's `[Symbol.replace]` calls: the
// whole match, each capture (a string where the group takes part in every
// match, else maybe `undefined`), the position, the input, and the `groups`
// object where a group is named. Its parameters may be fewer or wider.
export function decode(raw: string): string {
  return raw.replace(
    /\\u\{([0-9A-Fa-f]+)\}|\\u([0-9A-Fa-f]{4})/g,
    (_: string, point: unknown, unit: unknown) =>
      typeof point === "string"
        ? String.fromCodePoint(parseInt(point, 16))
        : String.fromCharCode(
            parseInt(typeof unit === "string" ? unit : "", 16),
          ),
  );
}

export function quote(path: string): string {
  return path.replace(/[\\"]/g, (c) => `\\${c}`);
}

// Group 1 takes part in every match: a string.
export function doubled(s: string): string {
  return s.replace(/(\d)/g, (_: string, d: string) => d + d);
}

export function positions(s: string): string {
  return s.replace(
    /x/g,
    (m: string, at: number, input: string) => `${m}${at}/${input.length}`,
  );
}

export function named(s: string): string {
  return s.replace(
    /(?<word>\w+)|-/g,
    (
      m: string,
      word: string | undefined,
      at: number,
      input: string,
      groups: { readonly [k: string]: string | undefined },
    ) => groups["word"] ?? `${m}${at}${input.length}${word ?? ""}`,
  );
}

export function every(s: string): string {
  return s.replaceAll(/(a)/g, (_: string, a: string) => a.toUpperCase());
}
