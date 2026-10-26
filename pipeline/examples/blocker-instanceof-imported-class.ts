// `instanceof` of an error class another module declares, as the front end
// tests its own failures.
// Census functions: files.mts#compilerFileSystem, array-prototype.mts#prototype,
// fragment-parse.mts#lowerFile, compiler-channel.mts#openFrontEndCompiler.
import { IoFailure } from "./blocker-instanceof-imported-class-failure.ts";
export function wrap(operation: string, run: () => string): string {
  try {
    return run();
  } catch (error) {
    throw error instanceof IoFailure ? error : new IoFailure(operation);
  }
}
