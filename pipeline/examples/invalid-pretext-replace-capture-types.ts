// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getCanvasFont.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim.
// A replacement callback typing as `string` the captures of the second
// alternative of its pattern: where the first alternative matches, a quoted
// family, the regex hands it `undefined` for each of them. Pretext reads
// them only where `quoted` is `undefined`; this case reads `separator` on
// the other arm too, which throws on `"Foo", serif` (run under Node).
const keywords = ["serif", "monospace"];

export function canvasFont(font: string, families: readonly string[]): string {
  return font.replace(
    /("[^"]*")|(^|,)(\s*)(serif|monospace)(?=\s*(?:,|$))/gi,
    (
      item: string,
      quoted: string | undefined,
      separator: string,
      space: string,
      keyword: string,
    ) => {
      if (quoted !== undefined) return item.slice(separator.length);
      const named = families[keywords.indexOf(keyword.toLowerCase())] ?? "";
      return named === "" ? item : separator + space + named;
    },
  );
}
