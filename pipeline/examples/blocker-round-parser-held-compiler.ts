// Census functions: fragment-parse.mts#projectFor, #openText, #openFile,
// #parseFile, #parseFragment; fragment-parse.mts#lowerModule, #lowerModuleText,
// #parseModules, #lowerFile. A compiler kept in a nullable module cell.
import type { API, Snapshot } from "typescript/unstable/sync";
let compiler: API | null = null;
let openings: number = 0;
const opened = new Set<string>();
export function update(api: API, absolute: string): Snapshot {
  if (!compiler) {
    const created = api;
    openings++;
    compiler = created;
  }
  const changed = opened.has(absolute);
  return changed
    ? compiler.updateSnapshot({
        openFiles: [absolute],
        fileChanges: { changed: [absolute] },
      })
    : compiler.updateSnapshot({ openFiles: [absolute] });
}
