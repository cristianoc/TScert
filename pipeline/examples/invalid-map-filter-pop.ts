// A `filter` callback popping the array being mapped, inside a `map`
// callback: `filter` is within its callback's footprint, which changes array
// stores arbitrarily, so `map` takes its signature with holes.
export function trimmed(lines: string[]): string[][] {
  return lines.map((l) =>
    l.split(" ").filter((w) => {
      lines.pop();
      return w !== "";
    }),
  );
}
