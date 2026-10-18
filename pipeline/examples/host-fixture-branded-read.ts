// A branded string the package produces is a string (reading rule 5).
import type { SourceFile } from "@fixture/host";

export function pathLength(f: SourceFile): number {
  return f.path.length;
}
