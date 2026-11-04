# Style: the design language

TScert communicates in four forms, with one visual and verbal language:

- **Commit record:** every commit carries one, a semantic diff rendered as
  a page (`make semantic-diff REV=…`; the record format is the
  [review skill](../.claude/skills/review/SKILL.md)).
- **Deep-dive deck:** a slide presentation that explains a design, a
  measurement or a piece of work end to end.
- **Card:** a single image that explains one fact for a post or a
  document.
- **Diagram:** a drawing in the documentation, such as
  [the architecture](../diagrams/architecture-light.png).

All four use the tokens and roles below, a colour means the same thing in
each, and the words follow [the voice](#the-voice).

## Tokens

The tokens are stated once, in
[`dev/style-tokens.mts`](../dev/style-tokens.mts): the record pages
([`dev/record-render.mts`](../dev/record-render.mts)) write them as CSS
variables, and a deck writes them inline.

| Token | Light | Dark | Role |
| --- | --- | --- | --- |
| `--bg` | `#fbfcfd` | `#0e1626` | page or slide background: cool white, or night navy |
| `--surface` | `#ffffff` | `#16213a` | cards |
| `--ink` | `#0b1a2e` | `#efe7d4` | text: navy ink, or cream |
| `--muted` | `#56627a` | `#9aa3b5` | labels, captions, secondary text |
| `--rule` | `#d5dce6` | `#2a3756` | borders and rules |
| `--accent` | `#8a6410` | `#e0ac4a` | rule names, emphasis: the gold, dark enough for text |
| `--code-bg` | `#eef2f7` | `#131d33` | code blocks |
| `--math-bg` | `#f2f4f8` | `#1a2540` | typeset rules and lowerings |

Typefaces, each served from Google Fonts as `FACES` states:
- Bricolage Grotesque for headings and the wordmark (`--display`), the
  identity's voice;
- Inter for text (`--body`);
- Source Code Pro for code (`--mono`), which has no ligatures, so code reads
  exactly as written;
- STIX Two Text for mathematics (`--math`).

The light scheme is cool white, and the dark scheme is its night (for video,
talks and banners). Both share navy, gold and the turnstile.

## Status colours

Each status colour is a pair, text on its tinted background, and always
comes with a word: colour never carries a meaning alone.

| Pair | Light text / background | Means |
| --- | --- | --- |
| `--ok` | `#2f6b47` / `#e2efe4` | added, verified, certified, a positive case |
| `--neg` | `#9b3524` / `#f5e1da` | removed, refused, a negative case |
| `--principled` | `#a0521a` / `#f7e6d6` | modified, a principled refusal, a forged control |
| `--gap` | `#6b6f78` / `#ecebe6` | a gap, a known limitation, stated but not certified |
| `--neutral` | `#2c4f7c` / `#e6ebf2` | no change in behaviour |
| `--trust` | `#7c2f4a` / `#f2e1e7` | a change of what is trusted |
| `--run` | `#7a5414` / `#f3e7cc` | code that runs: an operation, a call, a check |

## Identity

TScert's identity is crisp navy ink and gold on cool white. Its sign is a
gold turnstile `⊢` on navy, as in the [logo](../assets/logo.svg). The turnstile is the symbol of derivability, the
judgment TScert checks. Two tokens carry it:

- `--brand-ink`, `#0b1a2e` (navy): headlines, diagram ink and arrows on
  cards;
- `--brand-gold`, `#b8840f` (gold): the mark and the rule bar.

**The mark** is a small gold `⊢` placed beside the surprising step, once
per card. **The rule bar** is a thin gold line under a takeaway, which
reads as the conclusion of an inference rule. Both appear only in their
role.

## Roles

A box, an arrow or a highlight in a diagram or a card plays one role. Each
role has one pair and one form, the same in every diagram, card and deck.
The role is also stated in words (a label, a legend or the text), since
colour never carries a meaning alone.

| Role | Pair | Form | In an example | In TScert's architecture |
| --- | --- | --- | --- | --- |
| value | `--neutral` | rounded box | `x`, `[10, 20, 30]`, a node | the documents passed between stages |
| runs code | `--run` | rounded box, bold label | `await x`, `then(…)`, `isPositive(x)` | — |
| result | `--ok` | rounded box | `42`, the narrowed type | checked, with a proved consequence |
| hazard | `--neg` | the hazard mark on the step | a hole, a branch that says NO | refused |
| takeaway | `--brand-gold` | the rule bar | the card's moral | — |
| proposed | `--gap` | dashed border | — | untrusted proposals (producer, search) |
| trusted | `--trust` | solid border, trust word | an assumed contract | translation and contracts trusted on review |

Arrows are `--brand-ink` at 3 px on cards and `--ink` elsewhere: solid for
what happens, dashed for what may happen. The surprising step carries
[the mark](#identity).

## Cards

A card is 1600×900 (16:9, the size X and LinkedIn show uncropped) on
`--bg`, with 64 px margins. It explains one fact, and it is built from a
small spec (headline, code, diagram boxes and arrows, takeaway, credit)
rendered to SVG, so that it can be regenerated, edited and checked: its
code runs under Node, and its output matches what the card says.

The numbered card has five parts, top to bottom:

1. **Series label:** the series' name and number in a `--run` pill, such
   as "What sound checking must notice · 7". The series owns its
   numbering.
2. **Headline:** one question with a surprising answer, or one short
   claim, in Bricolage Grotesque at 700 weight and 64 px, with the mark beside it.
3. **Code, on the left:** at most 8 lines of TypeScript at 30 px Source Code Pro
   on `--code-bg`, highlighted with `SYNTAX`, ending in a comment that
   shows the observed result.
4. **Diagram, on the right:** what happens at run time, drawn in
   [roles](#roles).
5. **Takeaway band:** on `--principled-bg`, a round mark ("!" for a
   hazard, "✓" for a justification), one sentence in Bricolage Grotesque at 700 weight and
   34 px, and one plain sentence at 28 px.

A footer line at 22 px in `--muted` holds the credit, the work the card's
point rests on (from [REFERENCES](REFERENCES.md)), and "TScert" with the
card's subject.

The verdict card answers a yes/no question. It has the headline, a verdict
pill (`--neg` for "No, not in general", `--ok` for "Yes"), the cases as
tiles with a code line each, and a `--ok` band stating the conditions under
which the answer holds.

The TScert card links a fact to how TScert handles it. It has the headline
and the fact's code on the left. On the right is what TScert does with it:
the rule that decides it, typeset, and the outcome (the refusal's message,
or what verification requires). The footer names the rule's document and
the pipeline case that shows it.

**Mathematics.** A rule is typeset as in the documentation: premises side
by side, a bar with the rule's name beside it, and the conclusion beneath,
in STIX Two on `--math-bg`. Variables are italic, constructors are sans,
keywords are mono. A formula on a card is copied from its owning document
and never generated.

**Production.** A card has two layers rendered from its spec:
- the **surfaces**: panels, pills and boxes, with no character;
- the **glyphs**: every character, line, arrow and mark, exact by
  construction.

An image model (Krea 3, given an approved card as a style reference) may
finish the surfaces layer only. The glyphs are composited on top, so no
character comes from the model. Before a card is posted, its text is read
back by OCR and compared with its spec.

## The voice

The words follow [AGENTS.md's writing rules](../AGENTS.md): present fact,
positive, at the subject's level, exactly as strong as the evidence, and
said once. For cards and posts:

- **One fact per card,** in this order: concrete code, then what happens,
  then the moral.
- **Plain words:** "can run code", "the traversal is not stable".
  TScert's own terms appear only on a TScert card, each explained there.
- **Credit:** a card or post whose idea comes from published work names it
  from [REFERENCES](REFERENCES.md), and a longer piece has its own section
  for the work it builds on.
- **No overclaiming:** each claim states its strength (proved, cited,
  conjectured, or measured with its date and commit) and its scope (what
  the theorem covers, what is trusted). Nothing is said more strongly than
  the documentation states it.

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

- **Type scale:** title 88 px (cover only), heading 56–60 px in
  Bricolage Grotesque 700, card title 28–30 px in Inter 600, text 24–28 px, labels
  24 px Inter 600 in capitals with letter spacing in `--muted`, code 24
  px Source Code Pro. Nothing below 24 px.
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
