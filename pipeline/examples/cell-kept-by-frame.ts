// Pretext prepareRichInline: a field tested against `null`, then a call of a
// function that grows a module array (`ZEROS.push`), whose frame changes
// array spines by `grow` and keeps every value location. The field's
// location holds a value, so the call's frame respects the cell fact
// `sub.trims ∈ number[]`, and it holds at the statements after the call.
const ZEROS: number[] = [];

function grow(): void {
  ZEROS.push(0);
}

type Sub = { trims: number[] | null };

export function f(sub: Sub): number {
  if (sub.trims !== null) {
    const t = sub.trims.length;
    grow();
    return t + sub.trims.length;
  }
  return 0;
}
