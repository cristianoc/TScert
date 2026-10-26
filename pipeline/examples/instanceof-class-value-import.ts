// `x instanceof C` of a class declaration another module exports: the test
// reads the import binding, whose class's prototype its declaration creates,
// and looks for it along x's chain (SOURCE-CONTRACTS.md, "Imported classes
// and `instanceof`"). Named, renamed, default and re-exported imports; a
// derived class of that module; a generic one; a passed test drops the
// primitive arms; a test in the module initialization.
import Fault, {
  IoFailure,
  Pair as Twin,
  ParseFailure,
} from "@fixture/failures";
import { RelayedFailure } from "@fixture/failures-relay";

export function isFailure(x: unknown): boolean {
  return x instanceof IoFailure;
}
export function lineOf(x: ParseFailure | string | number): number {
  if (x instanceof ParseFailure) {
    return x.line;
  }
  return 0;
}
export function firstOf(x: Twin<number> | string): number {
  if (!(x instanceof Twin)) {
    return 0;
  }
  return x.first;
}
export function codeOf(x: Fault | null): number {
  return x instanceof Fault ? x.code : 0;
}
export function operationOf(x: IoFailure | boolean): string {
  return x instanceof RelayedFailure ? x.operation : "none";
}
export function wrap(operation: string, run: () => string): string {
  try {
    return run();
  } catch (error) {
    throw error instanceof IoFailure ? error : new IoFailure(operation);
  }
}
export function tests(): boolean {
  const p = new ParseFailure(3);
  return (
    p instanceof IoFailure &&
    !(new IoFailure("read") instanceof ParseFailure) &&
    !isFailure("read") &&
    lineOf(p) === 3
  );
}
const atStart: boolean = new IoFailure("start") instanceof RelayedFailure;
