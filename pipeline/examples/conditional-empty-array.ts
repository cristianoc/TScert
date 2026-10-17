// A conditional with an empty array literal in one arm, no type expected:
// the literal is built at the other arm's array type, as TypeScript types
// `c ? xs : []`, so the value is one array type whose length is read.
export function lineCount(text: string, keep: boolean): number {
  const lines = keep ? text.split("\n") : [];
  return lines.length;
}

export function firstWords(text: string): string[] {
  const words = text === "" ? [] : text.split(" ");
  return words.slice(0, 2);
}
