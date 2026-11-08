// pretext's `getCanvasFont`: a string's `replace` at a regex literal and a
// callback reading an array. The callback keeps every store, so the call is
// within `{value: any, store: keep}`, the regex's `lastIndex` its one write,
// and a loop calling the function keeps its bound.

const keywords: readonly string[] = ["serif", "monospace"];

export function canvasFont(font: string, families: readonly string[]): string {
  return font.replace(/(serif|monospace)/g, (item: string, keyword: string) => {
    const named = families[keywords.indexOf(keyword)] ?? "";
    return named === "" ? item : named;
  });
}

export function fonts(texts: string[], families: readonly string[]): number {
  let total = 0;
  for (let i = 0; i < texts.length; i++) {
    total += canvasFont(texts[i]!, families).length;
    total += texts[i]!.length;
  }
  return total;
}
