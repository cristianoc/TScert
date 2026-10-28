// A constructor assignment reading `this` needs the fields assigned before it
// read from the instance under construction.
// Census functions:
// fragment-parse.mts#diagnosticFragment, fragment-parse.mts#lowerFile,
// fragment-parse.mts#lowerModule, fragment-parse.mts#lowerModuleText,
// fragment-parse.mts#parseFile, fragment-parse.mts#parseFragment,
// fragment-parse.mts#parseModules.
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
