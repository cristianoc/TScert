// The document's root element read at `lang` as a string: an SVG document's
// root is no HTML element and has no `lang`, which reads `undefined`, and a
// document with no root answers `null` (run under Node with a stand-in
// document whose root has no `lang`).
export function language(): string {
  return document.documentElement.lang;
}
