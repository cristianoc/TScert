/* The deck kit: deep-dive decks (docs/STYLE.md, "Decks") written in the
 * slide format of claude.ai's Slides artifacts, in the commit-record pages'
 * style. A deck's source is `docs/deep-dives/<name>/deck.mts`, whose default
 * export is a `Deck` built from the blocks below; `deck-cli.mts` writes its
 * `project/` (the files the Slides viewer reads), checks them, and renders a
 * standalone page for viewing outside the viewer.
 *
 * The blocks draw what the record pages draw (`record-render.mts`): status
 * words, change blocks with their action, Before and After side by side,
 * formulas and inference rules by the roles of their tokens, lowerings,
 * highlighted TypeScript with added and removed lines, Effect lines. The
 * analyses are the record renderer's own (`mathTokens`, `mathRoles`,
 * `codeTokens`, `changeHead`, `versions`), and the colours and typefaces
 * are the shared tokens (`style-tokens.mts`). The Slides format admits
 * inline styles only, from a closed subset: no classes, no `<code>`, `<pre>`,
 * `<sub>` or `<sup>`, and no size or typeface on a span. So, where a record
 * page differs:
 * - inline code, and code inside a formula, takes the code colour in the
 *   surrounding typeface;
 * - a sub- or superscript is written with the Unicode sub- and superscript
 *   characters where every character has one, and as `_x` or `^x` otherwise;
 * - small capitals (a formula's constructors) are drawn by colour alone;
 * - a code block is one paragraph per line, its indentation non-breaking
 *   spaces, an added or removed line marked by its background;
 * - slides use the light colours: the format has no dark scheme. */
import {
  changeHead, codeTokens, dedent, mathRoles, mathTokens, parts, parseRecord, versions,
  CODE_KINDS, MATH_KINDS, PLAIN_KINDS, type CommitRecord, type MathRole, type Section,
} from "./record-render.mts";
import { FONTS, LIGHT, SYNTAX } from "./style-tokens.mts";

/** One slide: its id, and its `<section>` in the slide format. */
export type Slide = { id: string; html: string };
/** A deck: its title, its slides in order, and its outline, each part's
 * description and the id of its first slide. */
export type Deck = { title: string; slides: Slide[]; sections: { description: string; start: string }[] };

const C = LIGHT;
const SANS = `font-family:${FONTS.body.replace(/"/g, "'")}`;
const SERIF = `font-family:${FONTS.display.replace(/"/g, "'")}`;
const MONO = `font-family:${FONTS.mono.replace(/"/g, "'")}`;
const MATH = `font-family:${FONTS.math.replace(/"/g, "'")}`;

/** The typefaces a deck's index declares, as Google Fonts links. */
export const FACES: Readonly<Record<string, { family: string; href: string }>> = {
  "ibm-plex-sans": { family: "IBM Plex Sans", href: "https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;600&display=swap" },
  "ibm-plex-serif": { family: "IBM Plex Serif", href: "https://fonts.googleapis.com/css2?family=IBM+Plex+Serif:wght@400;500&display=swap" },
  "ibm-plex-mono": { family: "IBM Plex Mono", href: "https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;600&display=swap" },
  "stix-two-text": { family: "STIX Two Text", href: "https://fonts.googleapis.com/css2?family=STIX+Two+Text:ital,wght@0,400;0,600;1,400&display=swap" },
};

/** Text with HTML's special characters escaped. */
export const esc = (s: string): string =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

/** A colour span. */
export const color = (hex: string, html: string): string => `<span style="color:${hex}">${html}</span>`;

/** Prose: `code` in backticks takes the code colour, `**bold**` is bold. */
export const inline = (s: string): string =>
  esc(s).split("`").map((piece, i) => (i % 2 === 1 ? color(SYNTAX.t, piece) : piece)).join("").replace(/\*\*([^*]+)\*\*/g, "<b>$1</b>");

/** The status words, each in its pair's text colour (STYLE.md, "Status colours"). */
export type Status = "ok" | "neg" | "principled" | "gap" | "neutral" | "trust";
export const status = (kind: Status, word: string): string => color(C[kind], esc(word));

/** A status pill: the word on its pair's tinted background. */
export const pill = (kind: Status, word: string): string =>
  `<p style="font-size:24px;font-weight:600;letter-spacing:1px;text-transform:uppercase;color:${C[kind]};background:${C[`${kind}-bg`]};padding:6px 14px;border-radius:8px">${esc(word)}</p>`;

/** A label in capitals, above a heading. */
const label = (text: string): string =>
  `<p style="font-size:24px;color:${C.muted};font-weight:600;letter-spacing:2px;text-transform:uppercase">${text}</p>`;

/** A slide: a label, a heading and a body, in a column with the standard
 * 128 px margins; `tone: "code"` sets it on the second tone, for a slide
 * that sets a contrast. */
export function slide(id: string, o: { label: string; title: string; body: string; note?: string; gap?: number; tone?: "code" }): Slide {
  const lab = o.note
    ? `<div style="display:flex;gap:24px;align-items:baseline;flex-wrap:wrap">${label(o.label)}<p style="font-size:24px;color:${C.muted}">${o.note}</p></div>`
    : label(o.label);
  return { id, html: `<section id="${id}" style="background:${o.tone === "code" ? C["code-bg"] : C.bg};color:${C.ink};${SANS};padding:120px 128px;display:flex;flex-direction:column;gap:${o.gap ?? 24}px">
${lab}
<h2 style="${SERIF};font-size:56px;font-weight:500;line-height:1.15">${o.title}</h2>
${o.body}
</section>
` };
}

/** The cover: a label, the title, and a paragraph. */
export function cover(id: string, o: { label: string; title: string; text: string }): Slide {
  return { id, html: `<section id="${id}" style="background:${C.bg};color:${C.ink};${SANS};padding:128px;display:flex;flex-direction:column;gap:40px">
${label(o.label)}
<h1 style="${SERIF};font-size:88px;font-weight:500;line-height:1.1">${o.title}</h1>
<p style="font-size:28px;color:${C.ink};line-height:1.4;width:1500px">${o.text}</p>
</section>
` };
}

/** A paragraph of body text. */
export const para = (html: string, size: number = 26): string =>
  `<p style="font-size:${size}px;color:${C.ink};line-height:1.4">${html}</p>`;

/** A bulleted list. */
export const bullets = (items: string[], size: number = 24): string =>
  `<ul style="font-size:${size}px;color:${C.ink};line-height:1.36">\n${items.map(i => `<li>${i}</li>`).join("\n")}\n</ul>`;

/** A titled bullet: `**Title:** text`. */
export const point = (title: string, html: string): string => `<b style="font-weight:600">${title}:</b> ${html}`;

/** A card: a title over a paragraph, on the surface colour. */
export const card = (title: string, html: string): string =>
  `<div style="background:${C.surface};border:1px solid ${C.rule};border-radius:16px;padding:24px;display:flex;flex-direction:column;gap:6px">` +
  `<h3 style="font-size:28px;font-weight:600">${title}</h3><p style="font-size:24px;color:${C.ink};line-height:1.36">${html}</p></div>`;

/** A figure: a number in the heading typeface over its caption, on a card's
 * surface; the number takes its status's colour, by default the accent.
 * Figures side by side are `cards` of figures. */
export const stat = (value: string, html: string, kind?: Status): string =>
  `<div style="background:${C.surface};border:1px solid ${C.rule};border-radius:16px;padding:24px;display:flex;flex-direction:column;gap:6px">` +
  `<p style="${SERIF};font-size:56px;font-weight:500;color:${kind ? C[kind] : C.accent}">${value}</p>` +
  `<p style="font-size:24px;color:${C.ink};line-height:1.34">${html}</p></div>`;

/** Cards in equal columns. */
export const cards = (items: string[], cols: number = 3): string =>
  `<div style="display:grid;grid-template-columns:repeat(${cols}, 1fr);gap:20px">${items.join("")}</div>`;

/** A card whose body is blocks (paragraphs, code, lists), under a title
 * when one is given, on the surface colour. */
export const panel = (title: string, body: string): string =>
  `<div style="background:${C.surface};border:1px solid ${C.rule};border-radius:16px;padding:16px 22px;display:flex;flex-direction:column;gap:6px">` +
  (title ? `<h3 style="font-size:28px;font-weight:600">${title}</h3>` : "") + `${body}</div>`;

/** Blocks side by side, top-aligned, each column a stack of blocks; `shares`
 * gives the columns' relative widths, equal by default. */
export const columns = (items: string[], shares: number[] = []): string =>
  `<div style="display:grid;grid-template-columns:${items.map((_, i) => `minmax(0, ${shares[i] ?? 1}fr)`).join(" ")};gap:36px;align-items:start">` +
  items.map(i => `<div style="display:flex;flex-direction:column;gap:14px">${i}</div>`).join("") + `</div>`;

/** A table: its header, its rows, and each column's share of the width;
 * `compact` sets the cells' padding to 4 px by 12 px, for a table of many
 * wrapped rows. */
export function table(head: string[], rows: string[][], widths: number[], o: { compact?: boolean } = {}): string {
  const pad = o.compact ? ";padding:4px 12px" : "";
  const th = head.map((h, i) => `<th style="width:${widths[i] ?? 10}%;text-align:left;font-weight:600${pad}">${h}</th>`).join("");
  const td = pad ? `<td style="${pad.slice(1)}">` : "<td>";
  return `<table style="font-size:24px;color:${C.ink}">\n<tr>${th}</tr>\n${rows.map(r => `<tr>${r.map(c => `${td}${c}</td>`).join("")}</tr>`).join("\n")}\n</table>`;
}

/** Code in the mono typeface: one paragraph per line on the code background,
 * TypeScript highlighted by the record renderer's tokens over the whole
 * block (a comment spanning lines is a comment on each); `marks` gives a
 * line's mark, an added (`add`) or removed (`del`) line drawn on its pair's
 * background. */
export function code(lines: string[], marks: ("add" | "del" | "")[] = []): string {
  const tokenColour = { c: C.muted, s: SYNTAX.s, n: SYNTAX.n, k: SYNTAX.k, t: SYNTAX.t, "": "" };
  // The block is tokenized whole, so a comment or a template string that
  // spans lines keeps its colour on each, then cut back into its lines.
  const byLine: { kind: keyof typeof tokenColour; text: string }[][] = lines.map(() => []);
  let at = 0;
  for (const { kind, text } of codeTokens(lines.join("\n"))) {
    text.split("\n").forEach((piece, k) => {
      if (k > 0) at++;
      if (piece) byLine[at]?.push({ kind, text: piece });
    });
  }
  const line = (_: string, i: number): string => {
    const body = (byLine[i] ?? []).map(({ kind, text }) => {
      const e = esc(text).replace(/ /g, "&#160;");
      return kind === "c" ? `<i>${color(tokenColour.c, e)}</i>` : kind ? color(tokenColour[kind], e) : e;
    }).join("") || "&#160;";
    const mark = marks[i] ?? "";
    const bg = mark === "add" ? `;background:${C["ok-bg"]}` : mark === "del" ? `;background:${C["neg-bg"]}` : "";
    return `<p style="${MONO};font-size:24px;line-height:1.45;white-space:nowrap${bg}">${body}</p>`;
  };
  return `<div style="background:${C["code-bg"]};padding:16px 22px;border-radius:12px;display:flex;flex-direction:column">${lines.map(line).join("")}</div>`;
}

const SUB: Readonly<Record<string, string>> = Object.fromEntries([..."0123456789+-=()aeoxhklmnpstijruv"].map((c, i) =>
  [c, "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼᵣᵤᵥ"[i] ?? c]));
const SUP: Readonly<Record<string, string>> = Object.fromEntries([..."0123456789+-=()in"].map((c, i) =>
  [c, "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁱⁿ"[i] ?? c]));

/** A sub- or superscript in Unicode characters where each has one. */
function script(t: string): string {
  const sup = t.startsWith("^"), inner = t.replace(/^[_^]\{?|\}$/g, "");
  const table = sup ? SUP : SUB;
  return [...inner].every(ch => table[ch] !== undefined) ? [...inner].map(ch => table[ch] ?? ch).join("") : `${sup ? "^" : "_"}${inner}`;
}

/** A formula, its tokens drawn by the roles the record renderer gives them;
 * adjacent tokens of one style share one span. */
export function formula(text: string): string {
  const ts = mathTokens(text), roles = mathRoles(ts);
  const style: { [R in MathRole]: { colour: string; wrap: "" | "i" | "b" } } = {
    code: { colour: SYNTAX.t, wrap: "" }, str: { colour: SYNTAX.s, wrap: "" }, intr: { colour: SYNTAX.intr, wrap: "" },
    lit: { colour: SYNTAX.lit, wrap: "" }, script: { colour: "", wrap: "" }, refused: { colour: C.neg, wrap: "b" },
    kw: { colour: SYNTAX.kw, wrap: "b" }, op: { colour: SYNTAX.op, wrap: "" }, var: { colour: "", wrap: "i" },
    con: { colour: SYNTAX.con, wrap: "" }, bind: { colour: SYNTAX.bind, wrap: "" }, rel: { colour: C.accent, wrap: "" },
    text: { colour: C.muted, wrap: "" }, plain: { colour: "", wrap: "" },
  };
  const runs: { colour: string; wrap: "" | "i" | "b"; text: string }[] = [];
  ts.forEach((t, i) => {
    const r = roles[i] ?? "plain";
    const text = r === "code" ? t.text.slice(1, -1) : r === "script" ? script(t.text) : t.text;
    const { colour, wrap } = t.kind === "space" && runs.length ? (runs[runs.length - 1] ?? style.plain) : style[r];
    const last = runs[runs.length - 1];
    if (last && last.colour === colour && last.wrap === wrap) last.text += text;
    else runs.push({ colour, wrap, text });
  });
  return runs.map(({ colour, wrap, text }) => {
    const inner = colour ? color(colour, esc(text)) : esc(text);
    return wrap ? `<${wrap}>${inner}</${wrap}>` : inner;
  }).join("");
}

/** Lines of formulas, side by side where three or more spaces separate them. */
const formulaRows = (lines: string[]): string => `<div style="display:flex;flex-direction:column;gap:2px">${lines.map(l =>
  `<div style="display:flex;flex-wrap:wrap;gap:4px 40px${/^\s{2,}/.test(l) ? ";padding-left:48px" : ""}">` +
  parts(l).map(p => `<p style="${MATH};font-size:28px;line-height:1.35">${formula(p)}</p>`).join("") + `</div>`).join("")}</div>`;

/** A `Rule:` block, read as the record renderer reads it: groups separated by
 * blank lines, a group with a line of `─` an inference rule (premises above,
 * conclusion below, its name after the bar), any other group formulas. */
export function rules(block: string[]): string {
  let current: string[] = [];
  const groups: string[][] = [current];
  for (const line of block) {
    if (line.trim()) current.push(line);
    else if (current.length) groups.push(current = []);
  }
  const drawn = groups.filter(g => g.length).map(g => {
    const barLine = g.find(l => /^\s*─{3,}/.test(l));
    if (barLine === undefined) return g.some(l => l.includes("⇝")) ? lowering(g) : formulaRows(g);
    const bar = g.indexOf(barLine);
    const name = /\(([^()]+)\)\s*$/.exec(barLine)?.[1] ?? "";
    const premises = g.slice(0, bar).flatMap(parts);
    const conclusion = g.slice(bar + 1);
    return `<div style="display:flex;align-items:center;gap:20px"><div style="display:flex;flex-direction:column;align-items:center">` +
      `<div style="display:flex;flex-wrap:wrap;justify-content:center;gap:4px 40px;padding:0 8px 4px">${premises.map(p => `<p style="${MATH};font-size:28px">${formula(p)}</p>`).join("")}</div>` +
      `<div style="border-top:2px solid ${C.ink};align-self:stretch;padding-top:4px">${conclusion.map(l => `<p style="${MATH};font-size:28px;text-align:center">${formula(l.trim())}</p>`).join("")}</div></div>` +
      (name ? `<p style="${MATH};font-size:26px;color:${C.accent}">(${esc(name)})</p>` : "") + `</div>`;
  });
  return `<div style="display:flex;flex-direction:column;gap:18px;background:${C["math-bg"]};border-left:6px solid ${C.accent};border-radius:6px;padding:18px 24px">${drawn.join("")}</div>`;
}

/** A lowering: each `source ⇝ term` line is the TypeScript form mapped to
 * its term; `label: …` lines are side conditions. */
export function lowering(lines: string[]): string {
  return `<div style="display:flex;flex-direction:column;gap:8px">${lines.filter(l => l.trim()).map(l => {
    const body = l.trim(), arrow = body.indexOf("⇝");
    if (arrow < 0) return `<p style="${MATH};font-size:28px;padding-left:48px">${formula(body)}</p>`;
    return `<div style="display:flex;flex-wrap:wrap;align-items:baseline;gap:6px 16px">${code([body.slice(0, arrow).trim()])}` +
      `<p style="${MATH};font-size:28px">${color(C.accent, "⇝")} ${formula(body.slice(arrow + 1).trim())}</p></div>`;
  }).join("")}</div>`;
}

/** A section of a commit record drawn as a change: the action, the kind and
 * the target as a heading, its text, and its block drawn by its kind, Before
 * and After side by side. */
export function change(s: Section): string {
  const { kind, action, target } = changeHead(s.name);
  const act: Readonly<Record<string, Status>> = { added: "ok", removed: "neg", modified: "principled", replaced: "principled" };
  const actKind = act[action];
  const head = `<div style="display:flex;align-items:center;gap:14px">${actKind ? pill(actKind, action) : ""}` +
    `<p style="font-size:28px;font-weight:600">${esc(kind)}${target && !CODE_KINDS.has(kind) ? ` ${color(C.muted, inline(target))}` : ""}</p></div>`;
  const text = s.text.length ? para(inline(s.text.join(" ")), 24) : "";
  const lines = dedent(s.block);
  if (!lines.length) return head + text;
  if (kind === "Effect") return head + text + effects(lines);
  const draw = (body: string[], mark: "add" | "del" | "" = "", other: string[] = []): string =>
    kind === "Lowering" ? lowering(body) : MATH_KINDS.has(kind) ? rules(body)
    : CODE_KINDS.has(kind) ? code(body, body.map(l => (mark && !other.includes(l) ? mark : "")))
    : PLAIN_KINDS.has(kind) ? code(body)
    : body.join("\n").split(/\n\s*\n/).map(p => para(inline(p.replace(/\s+/g, " ").trim()), 24)).join("");
  const split = versions(lines);
  if (!split) return head + text + draw(lines);
  const figure = (caption: string, html: string): string =>
    `<div style="flex:1;display:flex;flex-direction:column;gap:6px">${label(caption)}${html}</div>`;
  return head + text + `<div style="display:flex;gap:20px">` +
    (split.before.length ? figure("Before", draw(split.before, "del", split.after)) : "") +
    (split.after.length ? figure("After", draw(split.after, "add", split.before)) : "") + `</div>`;
}

/** Effect lines: `case   kind   old → new   reason`, three or more spaces apart. */
export function effects(lines: string[]): string {
  const KINDS: Readonly<Record<string, Status>> = { positive: "ok", negative: "neg", gap: "gap", control: "principled" };
  return bullets(lines.filter(l => l.trim()).map(l => {
    const rest = parts(l);
    const what = rest.shift() ?? "";
    const first = rest[0];
    const kind = first !== undefined && KINDS[first] !== undefined ? rest.shift() : undefined;
    const next = rest[0];
    const outcome = next !== undefined && next.includes("→") ? rest.shift() ?? "" : "";
    const [old = "", now = ""] = outcome.split("→").map(x => x.trim());
    const kindStatus = kind === undefined ? undefined : KINDS[kind];
    return color(SYNTAX.t, esc(what)) + (kind && kindStatus ? ` ${status(kindStatus, kind)}` : "") +
      (outcome ? ` ${old.includes("⚠") ? `<b>${color(SYNTAX.unsound, inline(old))}</b>` : inline(old)} ${color(C.accent, "→")} <b>${inline(now)}</b>` : "") +
      (rest.length ? ` ${color(C.muted, rest.map(inline).join(" "))}` : "");
  }));
}

/** The record of a commit, parsed as the record pages parse it. */
export const record = (message: string, sha: string): CommitRecord =>
  parseRecord(message, { sha, author: "", stat: [], message });

/** A slide of a commit record's sections, the outcome as a pill beside the
 * subject. */
export function recordSlide(id: string, r: CommitRecord, sectionNames: string[] = r.sections.map(s => s.name)): Slide {
  const outcome = r.trailers.get("Outcome") ?? "";
  const pillKind: Readonly<Record<string, Status>> = { verified: "ok", refused: "principled", gap: "gap", "no-behaviour-change": "neutral" };
  const body = r.sections.filter(s => sectionNames.includes(s.name)).map(change).join("");
  return slide(id, { label: `Commit ${r.sha}`, title: inline(r.subject), body, note: outcome ? status(pillKind[outcome] ?? "neutral", outcome) : "", gap: 16 });
}

/** The deck's index, `project/deck.json`, as the Slides viewer reads it. */
export function index(deck: Deck, createdAt: string): string {
  return JSON.stringify({
    v: 4, createdOnFiles: { v: 1, at: createdAt }, lists: "css", title: deck.title, order: deck.slides.map(s => s.id),
    sections: Object.fromEntries(deck.sections.map((s, i) => [`s${i}`, s])), faces: FACES, designSystems: [],
  });
}

/** The tags the Slides format admits, and the CSS properties of its subset
 * (the type's `artifact-type/reference/format.md`, "Supported CSS"). */
const TAGS = new Set(["section", "h1", "h2", "h3", "p", "ul", "ol", "li", "br", "b", "i", "u", "a", "span", "div", "img",
  "table", "tr", "th", "td", "svg", "hr", "x-shape", "x-icon", "x-connector", "x-embed", "aside"]);
const PROPERTIES = new Set(("position left top right bottom width height min-width min-height max-width max-height display " +
  "flex-direction flex-wrap gap align-items justify-content justify-items align-self justify-self flex flex-grow flex-shrink " +
  "flex-basis grid-template-columns grid-template-rows grid-column grid-row aspect-ratio padding overflow font-family font-size " +
  "font-weight font-style font line-height letter-spacing text-align text-transform white-space text-decoration " +
  "font-variant-numeric -webkit-text-stroke color background background-clip border border-top border-right border-bottom " +
  "border-left border-radius box-shadow text-shadow opacity transform filter backdrop-filter mix-blend-mode object-fit").split(" "));

/** What a slide holds outside the format: an unknown tag or CSS property,
 * a font size below 24 px, more than 200 elements. */
export function check(s: Slide): string[] {
  const found: string[] = [];
  const tags = [...s.html.matchAll(/<([a-z][a-z0-9-]*)\b/g)].map(m => m[1] ?? "");
  for (const t of new Set(tags)) if (!TAGS.has(t) && !s.html.includes("<svg")) found.push(`${s.id}: the tag <${t}> is outside the format`);
  if (tags.length > 200) found.push(`${s.id}: ${tags.length} elements, more than 200`);
  for (const m of s.html.matchAll(/style="([^"]*)"/g)) {
    for (const decl of (m[1] ?? "").split(";")) {
      const prop = decl.split(":")[0]?.trim() ?? "";
      if (prop && !PROPERTIES.has(prop)) found.push(`${s.id}: the property ${prop} is outside the format`);
      const size = /^font-size:\s*(\d+)px/.exec(decl.trim());
      if (size && Number(size[1]) < 24) found.push(`${s.id}: a font size of ${size[1]} px, below 24`);
    }
  }
  if (!/<section id="([^"]+)"/.test(s.html) || /<section id="([^"]+)"/.exec(s.html)?.[1] !== s.id) found.push(`${s.id}: the section's id differs from the slide's`);
  return [...new Set(found)];
}

/** A standalone page of the deck for a browser: each slide on its
 * 1920×1080 canvas scaled to the window, the arrow keys moving between
 * them, the typefaces linked. */
/** A slide's HTML with what changed since `before`, the slide's HTML at an
 * earlier commit, marked for a reader comparing the two: every paragraph,
 * heading, list item and table cell whose text `before` does not hold gets
 * the mark colour, and a slide with any such block, or none before, a frame
 * and a "changed" or "new" tag. Unchanged slides come back as they are. */
export function markChanges(html: string, before: string | null): string {
  const text = (fragment: string): string => fragment.replace(/<[^>]*>/g, " ").replace(/&nbsp;|&#160;/g, " ")
    .replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&").replace(/\s+/g, " ").trim();
  const blocks = /<(p|h1|h2|h3|li|td|th)( style="[^"]*")?>([\s\S]*?)<\/\1>/g;
  const old = new Set<string>();
  if (before !== null) for (const m of before.matchAll(blocks)) old.add(text(m[3] ?? ""));
  let changed = 0;
  const marked = html.replace(blocks, (...groups: unknown[]): string => {
    const [whole, tag, style, inner] = groups.map(g => (typeof g === "string" ? g : ""));
    const t = text(inner ?? "");
    if (!t || old.has(t)) return whole ?? "";
    changed++;
    const own = style ? style.slice(8, -1) : "";
    return `<${tag ?? "p"} style="${own}${own ? ";" : ""}background:${SYNTAX.mark};box-shadow:-10px 0 0 ${SYNTAX.mark}">${inner ?? ""}</${tag ?? "p"}>`;
  });
  if (before !== null && changed === 0) return html;
  const tag = before === null ? "new" : "changed";
  return marked.replace(/^<section ([^>]*?)style="([^"]*)">/, (...groups: unknown[]): string => {
    const [, attrs, style] = groups.map(g => (typeof g === "string" ? g : ""));
    return `<section ${attrs ?? ""}style="${style ?? ""};box-shadow:inset 0 0 0 10px ${SYNTAX.mark}">` +
    `<p style="position:absolute;top:40px;right:128px;font-size:24px;font-weight:600;background:${SYNTAX.mark};color:#1d2422;padding:4px 14px;border-radius:8px">${tag}</p>`;
  });
}

/** A marked slide (`markChanges`) in the forms the Slides format keeps, for
 * a published copy: the frame becomes a bar pinned along the top edge, a
 * list holding a marked item becomes one paragraph per item, each opening
 * with "•", the marked ones keeping their fill, and a table holding a
 * marked cell, whose cells the format neither fills nor colours, becomes
 * rows of boxes: one flex row per table row, one box per cell at the first
 * row's column widths, its text a paragraph, a marked box filled. */
export function slidesForm(html: string): string {
  const fill = `background:${SYNTAX.mark}`;
  const frame = `;box-shadow:inset 0 0 0 10px ${SYNTAX.mark}"`;
  if (!html.includes(frame)) return html;
  let out = html.replace(frame, '"').replace(/^(<section [^>]*>)/,
    `$1<div style="position:absolute;left:0;top:0;width:1920px;height:12px;${fill}"></div>`);
  out = out.replace(/<(ul|ol) style="([^"]*)">([\s\S]*?)<\/\1>/g, (...groups: unknown[]): string => {
    const [whole, kind, style, body] = groups.map(g => (typeof g === "string" ? g : ""));
    const items = [...(body ?? "").matchAll(/<li( style="[^"]*")?>([\s\S]*?)<\/li>/g)];
    if (!items.some(m => (m[1] ?? "").includes(fill))) return whole ?? "";
    return `<div style="display:flex;flex-direction:column;gap:6px">` + items.map((m, i) =>
      `<p style="${style ?? ""}${(m[1] ?? "").includes(fill) ? ";" + fill : ""}">${kind === "ol" ? `${i + 1}.` : "•"} ${m[2] ?? ""}</p>`).join("") + "</div>";
  });
  return out.replace(/<table style="([^"]*)">([\s\S]*?)<\/table>/g, (...groups: unknown[]): string => {
    const [whole, tableStyle, body] = groups.map(g => (typeof g === "string" ? g : ""));
    if (!(body ?? "").includes(fill)) return whole ?? "";
    const rows = [...(body ?? "").matchAll(/<tr>([\s\S]*?)<\/tr>/g)].map(r =>
      [...(r[1] ?? "").matchAll(/<(td|th)( style="([^"]*)")?>([\s\S]*?)<\/\1>/g)]
        .map(c => ({ head: c[1] === "th", style: c[3] ?? "", inner: c[4] ?? "" })));
    const widths = (rows[0] ?? []).map(c => /width:([\d.]+)%/.exec(c.style)?.[1] ?? "");
    const stroke = `1px solid ${C.rule}`;
    return `<div style="display:flex;flex-direction:column">` + rows.map((row, r) =>
      `<div style="display:flex;flex-direction:row">` + row.map((cell, k) => {
        const width = widths[k] ? `width:${widths[k]}%;` : "flex:1;";
        const edges = `border:${stroke}${r > 0 ? ";border-top:none" : ""}${k > 0 ? ";border-left:none" : ""}`;
        const marked = cell.style.includes(fill) ? `;${fill}` : "";
        const weight = cell.head ? ";font-weight:600" : "";
        return `<div style="${width}padding:8px 14px;${edges}${marked}"><p style="${tableStyle ?? ""}${weight}">${cell.inner}</p></div>`;
      }).join("") + "</div>").join("") + "</div>";
  });
}

export function viewer(deck: Deck): string {
  const links = Object.values(FACES).map(f => `<link rel="stylesheet" href="${f.href}">`).join("\n");
  return `<!doctype html>
<html><head><meta charset="utf-8"><title>${esc(deck.title)}</title>
${links}
<style>
*{margin:0;box-sizing:border-box}html,body{height:100%;background:#2a2f2d}
#stage{position:fixed;inset:0;display:flex;align-items:center;justify-content:center}
section{width:1920px;height:1080px;flex:none;position:relative;transform-origin:center;overflow:hidden}
section:not(.on){display:none !important}ul,ol{padding-left:1.2em}li{margin:4px 0}td,th{padding:.35em .6em;border:1px solid ${C.rule};vertical-align:top}
table{border-collapse:collapse}#count{position:fixed;right:16px;bottom:12px;color:#cfd6d3;font:14px ${FONTS.body}}
</style></head><body><div id="stage">
${deck.slides.map(s => s.html).join("\n")}
</div><div id="count"></div>
<script>
const slides=[...document.querySelectorAll("section")];let i=Math.max(0,slides.findIndex(s=>"#"+s.id===location.hash));
function show(){slides.forEach((s,k)=>s.classList.toggle("on",k===i));const z=Math.min(innerWidth/1920,innerHeight/1080);
slides[i].style.transform="scale("+z+")";document.getElementById("count").textContent=(i+1)+" / "+slides.length;history.replaceState(null,"","#"+slides[i].id)}
addEventListener("keydown",e=>{if(["ArrowRight","PageDown"," "].includes(e.key))i=Math.min(slides.length-1,i+1);
else if(["ArrowLeft","PageUp"].includes(e.key))i=Math.max(0,i-1);else if(e.key==="Home")i=0;else if(e.key==="End")i=slides.length-1;else return;e.preventDefault();show()});
addEventListener("resize",show);show();
</script></body></html>
`;
}
