// A line walker whose visitor takes more parameters than the caller's
// closure declares, as pretext's src/line-break.ts exports
// `walkPreparedLinesRaw`.
export type LineData = { widths: number[] };

type LineVisitor = (width: number, start: number, end: number) => void;

export function walkLines(
  prepared: LineData,
  maxWidth: number,
  onLine?: LineVisitor,
): number {
  let lines = 0;
  for (let i = 0; i < prepared.widths.length; i++) {
    const width = prepared.widths[i]!;
    if (width <= maxWidth) {
      onLine?.(width, i, i + 1);
      lines++;
    }
  }
  return lines;
}
