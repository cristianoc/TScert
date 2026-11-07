// A 2D context's host accessors read and written through bracket access at
// a string key: TypeScript gives `context["font"]` and `context.font` one
// meaning, so each is the accessor's intrinsic, exactly as the dot spelling
// (SOURCE-CONTRACTS.md, the overlay of library types).
type Context = CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;

export function measureIn(
  context: Context,
  font: string,
  text: string,
): number {
  context["font"] = font;
  return context.measureText(text).width;
}

export function readsFont(context: Context): string {
  return context["font"];
}

export function setsKerning(context: Context): void {
  context["fontKerning"] = "none";
}
