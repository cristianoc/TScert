// A spread of a 2D context: its attributes are accessors on its interface's
// prototype, which a spread does not copy, so the copy has no `font`
// (run under Node with a stand-in whose class defines the accessor).
export function copied(context: CanvasRenderingContext2D): { font: string } {
  return { ...context };
}
