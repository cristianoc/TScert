// Census functions:
// fragment-parse.mts#projectFor
// fragment-parse.mts#openText
// fragment-parse.mts#openFile
import type { API, Snapshot } from "typescript/unstable/sync";
export function update(
  compiler: API,
  absolute: string,
  changed: boolean,
): Snapshot {
  return changed
    ? compiler.updateSnapshot({
        openFiles: [absolute],
        fileChanges: { changed: [absolute] },
      })
    : compiler.updateSnapshot({ openFiles: [absolute] });
}
