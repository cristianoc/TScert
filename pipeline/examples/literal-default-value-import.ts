// Imported declarations whose parameters state their types by literal
// defaults (`imports-project/literal-defaults.ts`), read at their declared
// signatures: each such parameter optional, at the literal's widened type.
import { Box, lineCount, scaled } from "@fixture/literal-defaults";

export function measure(width: number): number {
  const box = new Box();
  const named = new Box(2, "named");
  return (
    lineCount(width) +
    lineCount(width, true) +
    scaled(width) +
    scaled(width, 3) +
    box.width +
    named.label.length
  );
}
