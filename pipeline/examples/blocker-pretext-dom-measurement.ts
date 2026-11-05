// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#readEmojiWidth,
// measurement.ts#readWidthIn.
// Refusal: unsupported: missing field body (`readWidthIn`: missing field
// appendChild).
// A span measured in the page: `document.body`, `document.createElement`,
// the element's `style` and `textContent` written, `appendChild` and
// `removeChild` on a parent, `getBoundingClientRect()`. The reviewed entry
// for `document` states its root's `lang` alone, and no entry states an
// element's tree or layout members.
export function readWidth(font: string): number {
  const body = document.body as HTMLElement | null;
  if (body === null) return NaN;
  const span = document.createElement("span");
  span.style.setProperty("font", font, "important");
  span.textContent = "\u{1F600}";
  body.appendChild(span);
  const width = span.getBoundingClientRect().width;
  body.removeChild(span);
  return width;
}
