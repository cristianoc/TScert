// Node declares `console` as a variable and as a namespace of interfaces,
// which is no value: the global is the variable, read at the members used.
export function report(n: number): void {
  console.log(`n${n}`);
  console.error("done");
}
