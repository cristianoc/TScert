// A `reduce` callback popping the array being mapped, inside a `map`
// callback: `reduce` is within its callback's footprint, which changes array
// stores arbitrarily, so `map` takes its signature with holes.
export function lengths(lines: string[]): number[] {
  return lines.map((l) =>
    l.split(" ").reduce((total, w) => {
      lines.pop();
      return total + w.length;
    }, 0),
  );
}
