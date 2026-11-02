// A guard's type promise does not promise preservation of another array.
// Popping the outer map receiver leaves a hole in the claimed dense result.
export function broken(lines: string[]): string[][] {
  return lines.map((line) =>
    line.split(" ").filter((word): word is string => {
      lines.pop();
      return word !== "";
    }),
  );
}
