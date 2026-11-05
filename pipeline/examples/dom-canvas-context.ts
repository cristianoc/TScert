// A 2D context as pretext's measurement.ts uses one, read through the
// overlay of library types: a record field holding either context, its
// `font` written and read back, `letterSpacing` tested and written,
// `fontKerning` and `textRendering` written, a record field narrowed
// across the setters, which write no location the model holds, and
// `measureText`'s `TextMetrics` read at `width` and its ink edges.
type Context = CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;
export type State = { context: Context; font: string; letterSpacing: string };

export function measureIn(
  context: Context,
  font: string,
  text: string,
): number {
  context.font = font;
  return context.measureText(text).width;
}

export function takesFont(context: Context, font: string): boolean {
  context.font = "1px serif";
  context.font = font;
  if (context.font !== "1px serif") return true;
  context.font = "2px serif";
  context.font = font;
  return context.font !== "2px serif";
}

export function shaped(
  state: State,
  font: string,
  letterSpacing: string,
): Context {
  if (state.font !== font) state.context.font = state.font = font;
  if (state.letterSpacing !== letterSpacing)
    state.context.letterSpacing = state.letterSpacing = letterSpacing;
  return state.context;
}

export function takesLetterSpacing(context: Context): boolean {
  return typeof context.letterSpacing === "string";
}

export function sameInk(a: TextMetrics, b: TextMetrics): boolean {
  const bound = a.width / 0x400000;
  return (
    Math.abs(a.width - b.width) <= bound &&
    Math.abs(a.actualBoundingBoxLeft - b.actualBoundingBoxLeft) <= bound &&
    Math.abs(a.actualBoundingBoxRight - b.actualBoundingBoxRight) <= bound
  );
}

export function kerning(context: Context, probe: string): number {
  context.textRendering = "optimizeLegibility";
  const kerned = context.measureText(probe).width;
  context.fontKerning = "none";
  const unkerned: TextMetrics = context.measureText(probe);
  context.fontKerning = "auto";
  return kerned - unkerned.width;
}

export type Runs = { whole: Context | null };
export function wholeRun(
  runs: Runs,
  make: () => Context,
  font: string,
): Context {
  if (runs.whole === null) {
    runs.whole = make();
    runs.whole.textRendering = "optimizeLegibility";
  }
  runs.whole.font = font;
  return runs.whole;
}
