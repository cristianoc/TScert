// A sync API request whose argument may be an object of the program:
// `Program.getSourceFile` puts a `DocumentIdentifier` object into its payload
// and serializes it with `JSON.stringify`, which runs the object's `toJSON`.
// A `toJSON` popping the mapped array leaves a hole in `map`'s result, so the
// request is read at its declared signature, unrestricted, and the result's
// annotation is refused (run under Node: a hole).
import type { Program } from "typescript/unstable/sync";

export function wrong(program: Program, xs: number[]): number[] {
  const id = {
    uri: "file:///absent.ts",
    toJSON: (): string => {
      xs.pop();
      return "file:///absent.ts";
    },
  };
  const r: number[] = xs.map(() =>
    program.getSourceFile(id) === undefined ? 0 : 1,
  );
  return r;
}
