# Style: commit-record pages and deep-dive decks

TScert communicates work in two forms with one visual style. Every commit
carries a commit record, a semantic diff rendered as a page
(`make semantic-diff REV=…`; the record format is the
[review skill](../.claude/skills/review/SKILL.md)). From time to time a
topic gets a deep-dive deck: a slide presentation that explains a design,
a measurement or a piece of work end to end. Both use the tokens below,
and a colour means the same thing in both.

## Tokens

The tokens are stated once, in
[`dev/style-tokens.mts`](../dev/style-tokens.mts): the record pages
([`dev/record-render.mts`](../dev/record-render.mts)) write them as CSS
variables, and a deck writes them inline.

| Token | Light | Dark | Role |
| --- | --- | --- | --- |
| `--bg` | `#f6f7f5` | `#131816` | page or slide background |
| `--surface` | `#ffffff` | `#1b2220` | cards |
| `--ink` | `#1d2422` | `#e3e9e6` | text |
| `--muted` | `#5b6662` | `#9aa6a1` | labels, captions, secondary text |
| `--rule` | `#d9dedb` | `#2f3936` | borders and rules |
| `--accent` | `#1f6f66` | `#6cc3b6` | rule names, emphasis, the one accent |
| `--code-bg` | `#eef1ef` | `#222b28` | code blocks |
| `--math-bg` | `#f3f1ea` | `#24231d` | typeset rules and lowerings |

Typefaces: IBM Plex Serif for headings (`--display`), IBM Plex Sans for
text (`--body`), IBM Plex Mono for code (`--mono`), STIX Two Text for
mathematics (`--math`).

## Status colours

Each status colour is a pair, text on its tinted background, and always
comes with a word: colour never carries a meaning alone.

| Pair | Light text / background | Means |
| --- | --- | --- |
| `--ok` | `#2e7d4f` / `#e3f2e8` | added, verified, certified, a positive case |
| `--neg` | `#9a3a2a` / `#f7e4df` | removed, refused, a negative case |
| `--principled` | `#8a5a12` / `#f6ecd9` | modified, a principled refusal, a forged control |
| `--gap` | `#5e6870` / `#e8ebed` | a gap, a known limitation, stated but not certified |
| `--neutral` | `#2b5b9c` / `#e2eaf6` | no change in behaviour |
| `--trust` | `#8b2f4b` / `#f6e3ea` | a change of what is trusted |

## Decks

A deep dive is checked in and pushed. Its source is
`docs/deep-dives/<name>/deck.mts`, written with the deck kit
([`dev/deck.mts`](../dev/deck.mts)), and `make deck NAME=<name>` builds from
it the folder `docs/deep-dives/<name>/project/`: `deck.json` (the title,
slide order and typefaces) and one `slides/<id>.html` per slide, each one
`<section>` of the slide format of claude.ai's Slides artifacts, through
which the deck is published for viewing. The same command checks every
slide against the format's subset and its canvas (content within the
128 px margins, no font below 24 px, at most 200 elements) and writes a
standalone page of the deck for a browser; `OPEN=1` opens it.

The kit's blocks draw what the record pages draw, from the record
renderer's own analyses: status words and pills, change blocks with their
action and Before and After side by side, formulas and inference rules by
the roles of their tokens, lowerings, TypeScript highlighted by token with
added and removed lines, Effect lines, and a whole commit record
(`recordSlide`). Where the slide format has no means, its header states the
nearest form it draws instead: no sub- or superscript, no small capitals,
no typeface or size within a line. A deck that only reports a moment's status (what
changed since a push, a list of decisions to take) is not a deep dive and
is not checked in.

A slide is 1920×1080. The page's styles scale to it:

- **Type scale:** title 88 px (cover only), heading 56–60 px in Plex
  Serif 500, card title 28–30 px in Plex Sans 600, text 24–28 px, labels
  24 px Plex Sans 600 in capitals with letter spacing in `--muted`, code 24
  px Plex Mono. Nothing below 24 px.
- **Surfaces:** slides on `--bg`; a second tone of `--code-bg` for slides
  that set a contrast; cards on `--surface` with a 1 px `--rule` border and
  a 16 px radius; code on `--code-bg` with a 12 px radius; typeset rules on
  `--math-bg` with a 6 px `--accent` left border.
- **Statement slides:** at most one or two per deck, on the dark tokens.
- **Status:** a status in a table or card uses its pair's text colour and
  its word (verified, refused, gap, trust change), as the pages do.

## Writing and checking a deck

A deck is written for a reader who knows TypeScript but nothing of TScert,
reading strictly in order. Each slide explains every token a newcomer meets
there, on that slide or before it, or says on that slide where it is
explained: the words of the prose, and also every name, field, keyword,
literal value and option that appears in code, tables or diagrams.

A deck is handed to the owner only after an agent with access to the
repository checks every claim, number and code excerpt against its source,
and that each is labelled as measured, cited or estimated, to the strength
the source supports.

### A revised deck

A revised deck is read for what changed since the version the owner last
approved, the commit that checked that version in (its record names the
version before it). `make deck NAME=<name> SINCE=<commit>` builds as above
and, beside it, marks what differs from the slides at that commit: each
paragraph, heading, list item and table cell whose text the old slide does
not hold is filled with the mark colour (`SYNTAX.mark`), and a changed or
new slide gets a frame and a "changed" or "new" tag. The marks go to the
standalone page and to a marked copy of `project/` in the temporary
directory, never to the checked-in files. In that copy, for publishing as a
Slides artifact, the marks take forms the format keeps (`slidesForm`): the
frame is a bar along the top edge, a list holding a marked item is one
paragraph per item, and a table holding a marked cell is rows of boxes, one
per cell. The owner reads the marked copy; once approved, the unmarked
`project/` is committed and published to the deck's artifact.

### Converging

A review reports only **blocking** findings: a term the reader meets on a
slide without the explanation needed to follow that slide's point, a claim
not supported by its source, a contradiction between slides. Everything
else is a minor note, listed separately, that does not hold the deck back.

A blocking finding is resolved by cutting or simplifying first and by
adding text only where nothing can go; each slide keeps within its space
and the deck within its slide count unless a new slide replaces text
elsewhere.

After the first full review, a round checks only whether each earlier
blocking finding is resolved and whether the text changed since introduces a
new one. When those rounds are clear, one fresh reader reads the whole deck
once more; a blocking finding from that read goes through the same rounds.
After three rounds the deck goes to the owner with whatever blocking
findings remain, listed.
