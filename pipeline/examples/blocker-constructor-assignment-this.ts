// A constructor assignment reading `this` is refused: the instance is
// allocated at the constructor's end from one value per field. TScert's code
// avoids the construct (SOURCE-REWRITES.md, "A method call on the instance
// under construction").
export class Counter {
  readonly start: number;
  readonly next: number;
  constructor(start: number) {
    this.start = start;
    this.next = this.after();
  }
  after(): number {
    return this.start + 1;
  }
}
export function next(start: number): number {
  return new Counter(start).next;
}
