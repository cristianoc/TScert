// Each arm of a constructor's last `if` allocates its own instance: an arm
// that leaves `step` unassigned allocates it at `undefined`, which is not a
// number. (TypeScript accepts this with `step!`.)
class Counter {
  count: number;
  step!: number;
  constructor(start: number, step?: number) {
    this.count = start;
    if (step !== undefined) {
      this.step = step;
    }
  }
}
export function make(): number {
  return new Counter(1).step;
}
