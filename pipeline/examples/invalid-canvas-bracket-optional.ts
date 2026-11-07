// An optional chain at a bracket read of a 2D context's accessor: the
// construct is not the reviewed form (an optional chain reads through a
// saved object), and is refused as a fragment restriction, though the
// context is never nullish so the program is safe.
type Context = CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;

export function readsFont(context: Context): string {
  return context?.["font"];
}
