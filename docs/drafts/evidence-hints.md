# Draft: a proposal key without the claims

An open question of evidence reuse across verifier changes. Claims are
labelled **read** (in the code or document named), **observed** (with the
run) or **conjectured**.

## The existing mechanism this extends

**Evidence proposals** ([STAGE-STORE.md](../STAGE-STORE.md#evidence-proposals)):
under `TSCERT_EVIDENCE_REUSE=1`, a search whose key misses reuses an entry
referenced under its proposal key, the digest of its manifest without the
fields that identify the program that searched, and the current check
decides it. The proposal key keeps the search's inputs by digest, the
slice's claims among them.

## The question

With the statement-entry rule of 3303c669 the check reads no candidate
fact (read: its commit record), so evidence the check accepts with one set
of candidates it accepts with a larger one. The proposal key binds the
claims' bytes, so a producer change that only adds candidates misses
every proposal. A second lookup under a key without the claims, the check
deciding, would cover producer-only changes (126 s for five pretext files,
observed 2026-11-10) at one check per changed unit; claims that differ in
required facts make each such check a refusal followed by a search, which
can make the lookup a net loss (conjectured). It is to be measured, over
a producer-only change of pretext, before it is built: units whose
evidence the current check accepts under changed claims, and the time of
the extra checks.
