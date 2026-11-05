// Declarations whose parameters state their types by literal defaults, as
// `isolatedDeclarations` reads them (`literal-default-value-import`).
export function lineCount(width: number, singleLine = false): number {
  return singleLine ? 1 : width;
}
export const scaled = (x: number, factor = 2): number => x * factor;
export class Box {
  constructor(
    public width = 1,
    public label = "box",
  ) {}
}
