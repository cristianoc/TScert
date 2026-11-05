// The font a context held, narrowed before a write of `font`, asserted after
// it: the setter changes the font the getter answers, so the narrowing does
// not survive the write.
export function stale(
  context: CanvasRenderingContext2D,
  font: string,
): "10px serif" | undefined {
  if (context.font !== "10px serif") return undefined;
  context.font = font;
  return context.font as "10px serif";
}
