/* The visual tokens that commit-record pages (`record-render.mts`) and
 * deep-dive decks (`deck.mts`) share (docs/STYLE.md, "Tokens"): colours for
 * the light and the dark scheme, the status pairs, the typefaces, and the
 * colours of highlighted code and formulas. Each is stated once here; the
 * record page writes them as CSS variables, and a deck writes them inline,
 * as the Slides format requires. */

/** The colour tokens, by their CSS variable name without the leading `--`. */
export type ColourToken =
  | "bg" | "surface" | "ink" | "muted" | "rule" | "accent" | "code-bg" | "math-bg"
  | "ok" | "ok-bg" | "principled" | "principled-bg" | "gap" | "gap-bg" | "neutral" | "neutral-bg"
  | "trust" | "trust-bg" | "neg" | "neg-bg";

export const LIGHT: Readonly<Record<ColourToken, string>> = {
  bg: "#f6f7f5", surface: "#fff", ink: "#1d2422", muted: "#5b6662", rule: "#d9dedb", accent: "#1f6f66",
  "code-bg": "#eef1ef", "math-bg": "#f3f1ea",
  ok: "#2e7d4f", "ok-bg": "#e3f2e8", principled: "#8a5a12", "principled-bg": "#f6ecd9",
  gap: "#5e6870", "gap-bg": "#e8ebed", neutral: "#2b5b9c", "neutral-bg": "#e2eaf6",
  trust: "#8b2f4b", "trust-bg": "#f6e3ea", neg: "#9a3a2a", "neg-bg": "#f7e4df",
};

export const DARK: Readonly<Record<ColourToken, string>> = {
  bg: "#131816", surface: "#1b2220", ink: "#e3e9e6", muted: "#9aa6a1", rule: "#2f3936", accent: "#6cc3b6",
  "code-bg": "#222b28", "math-bg": "#24231d",
  ok: "#7fd3a0", "ok-bg": "#1f3428", principled: "#e3b46a", "principled-bg": "#382c17",
  gap: "#aab4bb", "gap-bg": "#2a3135", neutral: "#8fb3e8", "neutral-bg": "#1e2a3d",
  trust: "#ec97b1", "trust-bg": "#3a2029", neg: "#f0a493", "neg-bg": "#3a221d",
};

/** The typeface stacks: headings, text, code and formulas. */
export const FONTS: Readonly<Record<"display" | "body" | "mono" | "math", string>> = {
  display: `"IBM Plex Serif",Georgia,serif`,
  body: `"IBM Plex Sans","Helvetica Neue",Arial,sans-serif`,
  mono: `"IBM Plex Mono",Menlo,Consolas,monospace`,
  math: `"STIX Two Text","STIX Two Math","STIXGeneral","Cambria Math","Apple Symbols",Georgia,serif`,
};

/** The colours of highlighted TypeScript (`k` keyword, `s` string, `n`
 * number, `t` type name) and of the roles of a formula's tokens. */
export const SYNTAX: Readonly<Record<"k" | "s" | "n" | "t" | "op" | "con" | "kw" | "bind" | "intr" | "lit" | "unsound" | "mark", string>> = {
  k: "#8e3fb5", s: "#2b7a3d", n: "#b0601a", t: "#2b5b9c",
  op: "#2b5b9c", con: "#1f6f66", kw: "#8e3fb5", bind: "#8e3fb5", intr: "#2b5b9c", lit: "#8e3fb5",
  unsound: "#b3261e", mark: "#ffe08a",
};

/** A scheme's colours as CSS variable declarations, `--bg:#f6f7f5; …`. */
export const cssVariables = (scheme: Readonly<Record<ColourToken, string>>): string =>
  Object.entries(scheme).map(([name, value]) => `--${name}:${value}`).join("; ");
