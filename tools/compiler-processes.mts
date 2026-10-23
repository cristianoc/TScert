/* The observer of the front end's compiler processes (`compiler-channel.mts`):
 * told each one's process id when it has started and again just before it
 * ends, while it still runs, and the processes running now. Each process is
 * named by a generation of its own, which a reused process id does not
 * repeat. It is the measurement of their CPU time (`pipeline/stages.mts`),
 * which reads the processes and nothing a stage computes. */

/** A running compiler process: its generation and process id. */
export type LiveCompiler = { readonly generation: number; readonly pid: number };
type Observer = { started: (compiler: LiveCompiler) => void; ending: (compiler: LiveCompiler) => void };
let observer: Observer | null = null;
let generations: number = 0;
const live = new Map<number, LiveCompiler>();

/** Observe the compiler processes from now on, or none. */
export function observeCompilers(observe: Observer | null): void {
  observer = observe;
}

/** The compiler processes running now, oldest first. */
export const liveCompilers = (): LiveCompiler[] => [...live.values()];

/** A compiler process `pid` has started. */
export function compilerStarted(pid: number | undefined): void {
  if (pid === undefined) return;
  const compiler = { generation: ++generations, pid };
  live.set(pid, compiler);
  observer?.started(compiler);
}

/** A compiler process `pid` is about to end. */
export function compilerEnding(pid: number | undefined): void {
  if (pid === undefined) return;
  const compiler = live.get(pid);
  if (!compiler) return;
  live.delete(pid);
  observer?.ending(compiler);
}
