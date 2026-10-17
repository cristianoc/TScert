// A namespace member is an import binding, which no code writes: JavaScript
// throws a TypeError at `lib.limit = 3` in a module, and the write is
// refused where it is written.
import * as lib from "@fixture/lib";

export function reset(): void {
  // @ts-expect-error -- TypeScript also rejects the write
  lib.limit = 3;
}
