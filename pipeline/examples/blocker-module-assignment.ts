// Assignments to module bindings need modeled module storage.
// Census functions:
// compiler-processes.mts#compilerStarted, files.mts#fresh,
// files.mts#importLedger, files.mts#inconsistent, files.mts#inheritLedger,
// files.mts#kept, files.mts#nodeUnobservable, files.mts#note,
// files.mts#noteIn, files.mts#unobservable.
let generation: number = 0;
export function use(): void {
  generation++;
}
