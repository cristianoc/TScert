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

// A constant holding a conditional of a non-empty `split` and an empty
// literal, read only: the split's result has its required position, and the
// value is the readonly array of strings both arms meet.
export function lineCount(text: string, keep: boolean): number {
  const lines = keep ? text.split("\n") : [];
  return lines.length;
}

// A result something shrinks takes the general form: popped, through an
// alias, or held at an annotation of `string[]`.
export function popped(text: string): number {
  const cells = text.split(",");
  cells.pop();
  return cells.length;
}

export function aliasShrunk(text: string): number {
  const cells = text.split(",");
  const alias = cells;
  alias.pop();
  return cells.length;
}

export function annotated(text: string): number {
  const cells: string[] = text.split(",");
  return cells.length;
}
