/* Builds a deep-dive deck from its source (`deck.mts`): writes the deck's
 * `project/` (the index and one file per slide, as the Slides viewer reads
 * them), checks every slide against the format's subset and its canvas,
 * and writes a standalone page for viewing the deck in a browser.
 *
 *   node dev/deck-cli.mts gap-priorities           # write, check, write the page
 *   node dev/deck-cli.mts gap-priorities --open    # and open the page
 *   node dev/deck-cli.mts gap-priorities --since a479e5c   # the page marks what changed since a479e5c
 *
 * The layout check renders the slides in headless Chrome (`CHROME`, by
 * default the macOS application's path) and reports a slide whose content
 * passes the canvas's bottom margin, y 952, or its right margin, x 1792,
 * an inline SVG's parts measured by their drawn boxes; without Chrome it
 * says so. */
import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";
import { check, FACES, index, markChanges, slidesForm, viewer, type Deck } from "./deck.mts";

const [name, ...flags] = process.argv.slice(2);
const sinceAt = flags.indexOf("--since");
const since = sinceAt < 0 ? undefined : flags[sinceAt + 1];
if (!name || !/^[a-z0-9-]+$/.test(name)) throw Error("usage: deck-cli.mts <deck name> [--open] [--since REV]");
const root = resolve(import.meta.dirname, "..", "docs", "deep-dives", name);
const loaded: unknown = await import(pathToFileURL(join(root, "deck.mts")).href);
const isDeck = (v: unknown): v is Deck => !!v && typeof v === "object" && "slides" in v && Array.isArray(v.slides) && "title" in v;
const exported = loaded && typeof loaded === "object" && "default" in loaded ? loaded.default : undefined;
if (!isDeck(exported)) throw Error(`${name}/deck.mts has no default export of a Deck`);
const deck = exported;

// The index keeps the creation time it was first written with.
const project = join(root, "project"), slidesDir = join(project, "slides");
mkdirSync(slidesDir, { recursive: true });
const indexPath = join(project, "deck.json");
const previous = existsSync(indexPath) ? /"at":\s*"([^"]+)"/.exec(readFileSync(indexPath, "utf8"))?.[1] : undefined;
writeFileSync(indexPath, index(deck, previous ?? new Date().toISOString().replace(/\.\d+Z$/, "Z")));
const ids = new Set(deck.slides.map(s => s.id));
for (const f of readdirSync(slidesDir)) if (f.endsWith(".html") && !ids.has(f.slice(0, -5))) rmSync(join(slidesDir, f));
for (const s of deck.slides) writeFileSync(join(slidesDir, `${s.id}.html`), s.html);

const problems = deck.slides.flatMap(check);

// The layout: every slide on one page, each slide's lowest content edge
// measured from its top once the typefaces have loaded.
const chrome = process.env["CHROME"] ?? "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
const measured = join(tmpdir(), `tscert-deck-${name}-measure.html`);
writeFileSync(measured, `<!doctype html><html><head><meta charset="utf-8">${Object.values(FACES).map(f => `<link rel="stylesheet" href="${f.href}">`).join("")}
<style>*{margin:0;box-sizing:border-box}section{width:1920px;height:1080px;display:flex}ul,ol{padding-left:1.2em}li{margin:4px 0}td,th{padding:.35em .6em;vertical-align:top}table{border-collapse:collapse}</style></head><body>
${deck.slides.map(s => s.html).join("\n")}
<script>document.fonts.ready.then(()=>{const out={};for(const s of document.querySelectorAll("section")){const box=s.getBoundingClientRect();let b=0,w=0;
for(const e of s.querySelectorAll("*")){const r=e.getBoundingClientRect();if(r.height>0){b=Math.max(b,r.bottom-box.top);w=Math.max(w,(e instanceof SVGElement?r.right:r.left+e.scrollWidth)-box.left)}}out[s.id]=[Math.round(b),Math.round(w)]}
document.body.setAttribute("data-bottoms",JSON.stringify(out))})</script></body></html>`);
let layout: string = "not checked: no Chrome at " + chrome;
if (existsSync(chrome)) {
  const dom = execFileSync(chrome, ["--headless=new", "--disable-gpu", "--virtual-time-budget=10000", "--window-size=1920,1080", "--dump-dom",
    pathToFileURL(measured).href], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"], maxBuffer: 64 * 1024 * 1024 });
  const raw = /data-bottoms="([^"]*)"/.exec(dom)?.[1]?.replace(/&quot;/g, '"');
  const bottoms: unknown = raw ? JSON.parse(raw) : undefined;
  if (bottoms && typeof bottoms === "object") {
    for (const [id, edges] of Object.entries(bottoms)) {
      if (!Array.isArray(edges)) continue;
      const [y, x]: unknown[] = edges;
      if (typeof y === "number" && y > 952) problems.push(`${id}: content reaches y ${y}, past the bottom margin at 952`);
      if (typeof x === "number" && x > 1792) problems.push(`${id}: content reaches x ${x}, past the right margin at 1792`);
    }
    layout = "checked";
  } else layout = "not checked: Chrome reported no measurement";
}

// With --since, the page and a marked copy of the project show what
// changed since that commit, the copy in the forms the Slides format keeps
// (`slidesForm`); the project's own files stay unmarked.
let shown: Deck = deck;
if (since) {
  if (!/^[0-9A-Za-z._/-]+$/.test(since)) throw Error(`--since takes a commit: ${since}`);
  const repository = resolve(import.meta.dirname, "..");
  const at = (id: string): string | null => {
    try {
      return execFileSync("git", ["-C", repository, "show", `${since}:docs/deep-dives/${name}/project/slides/${id}.html`],
        { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] });
    } catch {
      return null;
    }
  };
  shown = { ...deck, slides: deck.slides.map(s => ({ ...s, html: markChanges(s.html, at(s.id)) })) };
  const marked = join(tmpdir(), `tscert-deck-${name}-since`, "project");
  rmSync(marked, { recursive: true, force: true });
  mkdirSync(join(marked, "slides"), { recursive: true });
  writeFileSync(join(marked, "deck.json"), readFileSync(indexPath, "utf8"));
  for (const s of shown.slides) writeFileSync(join(marked, "slides", `${s.id}.html`), slidesForm(s.html));
  const changed = shown.slides.filter((s, i) => s.html !== deck.slides[i]?.html).map(s => s.id);
  process.stdout.write(`marked since ${since}: ${changed.length ? changed.join(", ") : "no slide"}; marked project: ${marked}\n`);
}
const page = join(tmpdir(), `tscert-deck-${name}.html`);
writeFileSync(page, viewer(shown));
process.stdout.write(`${deck.slides.length} slides written to ${project}\nlayout ${layout}\n${problems.length ? problems.join("\n") : "no problems"}\npage: ${page}\n`);
if (flags.includes("--open")) execFileSync("open", [page]);
if (problems.length) process.exitCode = 1;
