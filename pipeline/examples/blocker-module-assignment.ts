// An update or a logical assignment of a module cell: the checked access
// reads the cell, then the value, checked at the cell's contract, is
// written. A function declared above the cell writes it, as `kept` writes
// `queryFailure`.
// Census functions:
// compiler-processes.mts#compilerStarted, compiler-channel.mts#useInstallationForTests,
// declaration-session.mts#inDeclarationSession, files.mts#fresh,
// files.mts#importLedger, files.mts#inconsistent, files.mts#inheritLedger,
// files.mts#kept, files.mts#nodeUnobservable, files.mts#note,
// files.mts#noteIn, files.mts#observeResolution, files.mts#unobservable,
// fragment-parse.mts#openFile.
let generation: number = 0;
export function use(): void {
  generation++;
}
export function next(): { generation: number } {
  return { generation: ++generation };
}
export function release(): void {
  generation--;
}

export function kept(error: unknown): void {
  failure ??= error;
}
let failure: unknown = null;

let reason: string | null = null;
export function retire(why: string): string {
  reason ??= why;
  return reason;
}
