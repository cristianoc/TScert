/* The observer of the front end's compiler processes (`compiler-channel.mts`):
 * told each one's process id when it has started and again just before it
 * ends, while it still runs. It is the measurement of their CPU time
 * (`pipeline/stages.mts`), which reads the process and nothing a stage
 * computes. */

type Observer = { started: (pid: number) => void; ending: (pid: number) => void };
let observer: Observer | null = null;

/** Observe the compiler processes from now on, or none. */
export function observeCompilers(observe: Observer | null): void {
  observer = observe;
}

/** A compiler process `pid` has started. */
export function compilerStarted(pid: number | undefined): void {
  if (observer && pid !== undefined) observer.started(pid);
}

/** A compiler process `pid` is about to end. */
export function compilerEnding(pid: number | undefined): void {
  if (observer && pid !== undefined) observer.ending(pid);
}
