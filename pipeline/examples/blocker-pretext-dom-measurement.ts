// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#readEmojiWidth,
// measurement.ts#readWidthIn.
// Refusal: reject: source expression obligation (the read of `span.style`,
// which is `undefined` for a span of a non-HTML document).
// A span measured in the page, in pretext's original form: the element's
// `style` written with no check. The form the rewrites of issue #94 use
// checks `style` first and verifies: see `pretext-host-span`.
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
