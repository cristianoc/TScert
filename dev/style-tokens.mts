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
  | "trust" | "trust-bg" | "neg" | "neg-bg" | "run" | "run-bg" | "brand-ink" | "brand-gold";

export const LIGHT: Readonly<Record<ColourToken, string>> = {
  bg: "#fbfcfd", surface: "#ffffff", ink: "#0b1a2e", muted: "#56627a", rule: "#d5dce6", accent: "#8a6410",
  "code-bg": "#eef2f7", "math-bg": "#f2f4f8",
  ok: "#2f6b47", "ok-bg": "#e2efe4", principled: "#a0521a", "principled-bg": "#f7e6d6",
  gap: "#6b6f78", "gap-bg": "#ecebe6", neutral: "#2c4f7c", "neutral-bg": "#e6ebf2",
  trust: "#7c2f4a", "trust-bg": "#f2e1e7", neg: "#9b3524", "neg-bg": "#f5e1da",
  run: "#7a5414", "run-bg": "#f3e7cc", "brand-ink": "#0b1a2e", "brand-gold": "#b8840f",
};

export const DARK: Readonly<Record<ColourToken, string>> = {
  bg: "#0e1626", surface: "#16213a", ink: "#efe7d4", muted: "#9aa3b5", rule: "#2a3756", accent: "#e0ac4a",
  "code-bg": "#131d33", "math-bg": "#1a2540",
  ok: "#7fd0a2", "ok-bg": "#17322a", principled: "#f0a868", "principled-bg": "#3a2a1c",
  gap: "#9aa3b5", "gap-bg": "#1c2639", neutral: "#8fb4e8", "neutral-bg": "#1b2b49",
  trust: "#e79bb6", "trust-bg": "#3a2131", neg: "#f0907d", "neg-bg": "#3a1f22",
  run: "#e0ac4a", "run-bg": "#2e2a24", "brand-ink": "#efe7d4", "brand-gold": "#e0ac4a",
};

/** The typefaces, each with the Google Fonts stylesheet that serves it. */
export const FACES: Readonly<Record<"bricolage-grotesque" | "inter" | "source-code-pro" | "stix-two-text", { family: string; href: string }>> = {
  "bricolage-grotesque": {
    family: "Bricolage Grotesque",
    href: "https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,500;12..96,700&display=swap",
  },
  inter: { family: "Inter", href: "https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap" },
  "source-code-pro": { family: "Source Code Pro", href: "https://fonts.googleapis.com/css2?family=Source+Code+Pro:wght@400;600&display=swap" },
  "stix-two-text": { family: "STIX Two Text", href: "https://fonts.googleapis.com/css2?family=STIX+Two+Text:ital,wght@0,400;0,600;1,400&display=swap" },
};

/** The typeface stacks: headings, text, code and formulas. */
export const FONTS: Readonly<Record<"display" | "body" | "mono" | "math", string>> = {
  display: `"Bricolage Grotesque","Helvetica Neue",Arial,sans-serif`,
  body: `"Inter","Helvetica Neue",Arial,sans-serif`,
  mono: `"Source Code Pro",Menlo,Consolas,monospace`,
  math: `"STIX Two Text","STIX Two Math","STIXGeneral","Cambria Math","Apple Symbols",Georgia,serif`,
};

/** The colours of highlighted TypeScript (`k` keyword, `s` string, `n`
 * number, `t` type name) and of the roles of a formula's tokens. */
export const SYNTAX: Readonly<Record<"k" | "s" | "n" | "t" | "op" | "con" | "kw" | "bind" | "intr" | "lit" | "unsound" | "mark", string>> = {
  k: "#7a3b8c", s: "#2f6b47", n: "#a35a12", t: "#2c4f7c",
  op: "#2c4f7c", con: "#8f6416", kw: "#7a3b8c", bind: "#7a3b8c", intr: "#2c4f7c", lit: "#7a3b8c",
  unsound: "#b3261e", mark: "#ffe08a",
};

/** A scheme's colours as CSS variable declarations, `--bg:#fbfcfd; …`. */
export const cssVariables = (scheme: Readonly<Record<ColourToken, string>>): string =>
  Object.entries(scheme).map(([name, value]) => `--${name}:${value}`).join("; ");
