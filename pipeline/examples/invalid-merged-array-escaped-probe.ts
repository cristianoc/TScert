// Another module of the project merges `toJSON(): undefined` into `Array`.
// This file declares an interface whose escaped name reads as the one the
// reviewed signatures are appended under, stating that `toJSON`: the
// reviewed interface is the appended text at its own position, so the
// client's declaration is not read as it and the merge is refused. The
// formatter would decode the escape, which is the point of the control.
// prettier-ignore
interface __TScertReviewe\u00640<T> {
  toJSON(): undefined;
  at(index: number): T | undefined;
}
export function text(xs: number[]): string {
  return JSON.stringify(xs);
}
