// Census functions: files.mts#observed,#observedNoting,#remembered,#nodeResolve,#resolveObserved.
// A recording has an own stage key exactly when the stage flag is true.
import type { Recording } from "../../tools/files.mts";
export function recording(stage: boolean, staleProcess: string | null): Recording {
  const made: Recording = { answers: new Map(), holding: new Set(), incomplete: null,
    inconsistent: staleProcess, ledger: false, readsInput: false };
  if (stage) made.stage = true;
  return made;
}
