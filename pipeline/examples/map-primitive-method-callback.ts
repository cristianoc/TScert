// Callbacks that read and allocate and call members stated heap-preserving:
// a string's methods, through `String.prototype`, and an array's readers.
// Each callback is certified preserving, so `map` takes its dense overload
// and the result is a readable `string[]`.
export function trimmed(lines: string[]): string[] {
  return lines.map((l: string): string => l.trim());
}

// A chain of members, an element read and a coalescing default.
export function firstWords(lines: string[]): string[] {
  return lines.map((l) => l.trim().toLowerCase().split(" ")[0] ?? "");
}

// Array readers inside the callback: `split`'s fresh array joined, sliced
// and searched.
export function joined(lines: string[]): string[] {
  return lines.map(
    (l) =>
      l.split(",").slice(1).join(";") + (l.split(",").includes("x") ? "!" : ""),
  );
}

// A parameter pattern reads positions; a number's method; a block body.
type Pair = [string, number];
export function labels(pairs: Pair[]): string[] {
  return pairs.map(([name, n]: Pair) => {
    const digits = n.toFixed(1);
    return name.length === 0 ? digits : `${name.toUpperCase()}=${digits}`;
  });
}
