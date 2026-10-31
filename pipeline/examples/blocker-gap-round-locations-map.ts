// Two maps resolving declarations and serializing locations.
// Census function: type-probe.mts#makeProbe.
import type { Symbol } from "typescript/unstable/sync";
import type { Node } from "typescript/unstable/ast";
export function locations(symbol: Symbol | undefined, map: boolean): string[] {
  const where = (node: Node): readonly (string | number)[] | string => {
    const file = node.getSourceFile();
    const start = node.getStart(file);
    return map && start < 0 ? "the probe" : [file.fileName, start, node.end];
  };
  return (symbol?.declarations ?? [])
    .map((d) => {
      const node = d.resolve();
      return node ? where(node) : null;
    })
    .map((d) => JSON.stringify(d));
}
