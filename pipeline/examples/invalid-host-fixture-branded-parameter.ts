// A host parameter of a branded string type is refused (L5): only the
// package produces its values, which the calculus cannot state.
import { fileAt, type SourceFile } from "@fixture/host";

export function again(f: SourceFile): SourceFile | undefined {
  return fileAt(f.path);
}
