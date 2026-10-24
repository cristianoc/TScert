# Style: commit-record pages and deep-dive decks

TScert communicates work in two forms with one visual style. Every commit
carries a commit record, a semantic diff rendered as a page
(`make semantic-diff REV=…`; the record format is the
[review skill](../.claude/skills/review/SKILL.md)). From time to time a
topic gets a deep-dive deck: a slide presentation that explains a design,
a measurement or a piece of work end to end. Both use the tokens below,
and a colour means the same thing in both.

## Tokens

The tokens are the `CSS` constant of
[`dev/record-render.mts`](../dev/record-render.mts), which owns them; a
deck copies their values.

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

A deep dive is checked in and pushed: its source is a folder
`docs/deep-dives/<name>/project/`, holding `deck.json` (the title, slide
order and typefaces) and one `slides/<id>.html` per slide, each one `<section>` of
the slide format of claude.ai's Slides artifacts, through which the deck is
published for viewing. A deck that only reports a moment's status (what
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

## Validating a deck

A deck is handed to the owner only after independent validation:

1. **Against the sources.** An agent with access to the repository checks
   every claim, number and code excerpt against its source, and that each
   is labelled as measured, cited or estimated, to the strength the source
   supports.
2. **With zero context.** A fresh agent reads only the slides, knowing
   TypeScript but nothing of TScert, and reports every term used before it
   is explained and every claim it cannot follow, with its own summary of
   what the deck says. It reads strictly in order and judges each slide
   only by what the slides up to it have said: an explanation on a later
   slide does not count unless the slide itself says where it comes. Every
   token on a slide is in scope: words of the prose, and also every name,
   field, keyword, literal value and option that appears in code, tables or
   diagrams. For each slide it lists the tokens a newcomer meets there
   without an explanation, or a forward pointer, on that slide or before
   it.

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
