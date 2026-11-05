// A 2D context made as pretext's measurement.ts makes one: from an
// `OffscreenCanvas` where the host defines one, else from a canvas element
// of the document, its `lang` set where it has the attribute; and the
// engine read from `navigator.userAgent` where the host defines one, and its
// platform from `navigator.platform`.
type Context = CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;

export function createContext(language: string | null): Context {
  let context: Context | null = null;
  if (typeof OffscreenCanvas !== "undefined")
    context = new OffscreenCanvas(1, 1).getContext("2d");
  else if (typeof document !== "undefined")
    context = document.createElement("canvas").getContext("2d");
  if (context === null)
    throw new Error(
      "Text measurement requires OffscreenCanvas or a DOM canvas context.",
    );
  if (language !== null && "lang" in context) context.lang = language;
  return context;
}

export function userAgent(): string {
  return typeof navigator === "undefined" ? "" : navigator.userAgent;
}

export function namesFamilies(engine: string): boolean {
  return (
    engine === "webkit" && !/^(?:Linux|Win32|Haiku|$)/.test(navigator.platform)
  );
}
