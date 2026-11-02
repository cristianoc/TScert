/*
 * Type stripping, for the suites that run a fragment source rather than check
 * it: a `.ts` corpus file is concatenated with others and evaluated in a `vm`
 * context to observe what the program actually does, and evaluation needs the
 * annotations gone.
 *
 * Nothing here compiles: the fragment is already JavaScript once the types are
 * erased. Both runtimes this repository uses erase types themselves — bun
 * through its own transpiler, node through the same stripper it applies to a
 * `.ts` entry point — so neither a compiler nor a build step is involved.
 */
import * as nodeModule from "node:module";

declare const Bun:
  | { Transpiler: new (o: { loader: string }) => { transformSync(s: string): string } }
  | undefined;

const strip: (source: string) => string = (() => {
  if (typeof Bun !== "undefined") {
    const transpiler = new Bun.Transpiler({ loader: "ts" });
    return (source: string) => transpiler.transformSync(source);
  }
  // Node's declared export, checked for runtimes where it is absent.
  const available: unknown = nodeModule.stripTypeScriptTypes;
  if (typeof available !== "function")
    throw Error("this runtime cannot erase type annotations");
  return (source: string): string => {
    const stripped = nodeModule.stripTypeScriptTypes(source);
    return String(stripped);
  };
})();

/** The source with its type annotations erased, ready to evaluate. */
export function stripTypes(source: string): string {
  return strip(source);
}
