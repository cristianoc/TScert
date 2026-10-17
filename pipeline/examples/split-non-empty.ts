// `split` at a non-empty string separator and no limit returns at least one
// element: element 0 of its result is a string, at a literal separator and
// at a union of non-empty literals.
type Record_ = { subject: string };

export function firstLine(text: string): Record_ {
  const lines = text.trimEnd().split("\n");
  return { subject: lines[0] };
}

export function firstField(text: string, semi: boolean): string {
  const fields = text.split(semi ? ";" : ",");
  return fields[0];
}

export function firstWord(text: string): string {
  return text.split(" ")[0].toUpperCase();
}

// Beside an empty literal in a conditional, the result and the literal are
// read at the readonly array of strings, which both meet.
export function lastLines(ps: string[]): number {
  const lines = ps.length > 1 ? ps[ps.length - 1].split("\n") : [];
  return lines.length;
}
