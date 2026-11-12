# Draft: the note "Tolerant frames" against the model

The claims of the working note "Tolerant frames" (11 November 2026) that the
indexed model states differently, each with the Lean theorem that replaces it,
so that the note can be revised from this list. Each item gives the note's
claim, the model's statement, and its label: **proved** (Lean name),
**false as stated** (a Lean counter-model), or **not formalized** (observed in
the definitions). The theorems are in
`lean/Verification/Programs/TolerantFramesModelLoop.lean`,
`TolerantFramesModelTyped.lean` and `TolerantFramesModelRules.lean` (namespace
`Verification.TolerantFrames`), beside the modules
[the Lean reading of the note](tolerant-frames-lean.md) owns. The
differences in the model's states and transitions themselves are listed in
[what the model requires beyond the note](tolerant-frames-lean.md#what-the-model-requires-beyond-the-note).

## Well-formed states

- **Allocated cells.** The note assumes every state well-formed: typed roots,
  every listed element cell allocated. In the model allocated cells are a fact
  of the world, $`\mathrm{StoreCells}(x)`$: $`x`$'s store location has a
  contract every store of which lists only cells of its world. A typed
  environment gives it where $`x`$'s type is a record whose store field has a
  type of one `.list` clause (proved: `storeCells_of_typed`; every element
  write the pass checks has such a type, `storeCells_of_storeField`), and for
  an object of a record, dictionary or `source` clause owning the store key in
  a graph stating the built-ins (proved: `storeCells_of_builtins`). Without
  the built-ins the array invariant states only that the store field holds a
  list (`PositiveGraphs.storeListT`), and no allocated cells follow (not
  formalized).
- **Class evidence.** A field of source-value type holds a value, not a store,
  and a store field of a `.list` type holds a store, at every heap meeting the
  world (proved: `valueClass_ok`, `storeClass_ok`); law (c) for footprints
  compared through that evidence then holds from every typed state (proved:
  `action_le_valueClass`).
- **Rigid paths.** "A path through `@stable` fields is rigid": a field every
  clause of the slot's type states stable reads one value in every admissible
  successor (proved: `stableAt_of_stableField`, and from the field rules'
  evidence `stableAt_of_stableFirst`); longer paths compose through a slot
  holding the intermediate value (proved: `stableAt_cons`), so (Grow) at a
  typed stable field needs no further premise (proved: `grow_path_typed`).

## The atoms

- **(View)** $`a(\mathrm{view}(w))\vdash\Box_\top\,a(\mathrm{view}(w))`$
  holds where $`w`$'s view-length key is read at a location whose contract
  admits one value, $`\mathrm{ViewStable}(w)`$, for a linear fact over slots'
  integers and such lengths (proved: `view_box`); a type stating the view
  length stable gives $`\mathrm{ViewStable}(w)`$ (proved:
  `viewStable_of_typed`). A typed array's length is not single-valued by being
  a typed array's: in a world whose locations admit every value, a transition
  changes it from 1 to 2 (false as stated: `view_not_invariant`).
- **(Init)** $`a(|\pi|)\vdash\Box_{\{\mathsf{values}:\mathsf{init},\ \mathsf{stores}:\mathsf{keep}\}}\,a(|\pi|)`$
  holds for every linear fact over integers, array lengths and view lengths at
  any paths, with no condition on the fields $`\pi`$ passes (proved:
  `init_box`, `init_path`): a defined path read passes only fields holding
  objects, which $`\mathsf{init}`$ keeps. A string length at a path is outside
  it: the model's kept-change test treats a string's location as altered.

## The rules

- **Call.** A callee checked from its entry at the environment
  $`\rho_c`$, its normal post bounding the heap by a regional effect
  $`\Phi`$ read at $`\rho_c`$, each callee position $`i`$ holding the caller's
  slot $`\sigma(i)`$: a run to the result $`v`$ is an action of
  $`\Phi[\sigma]`$ at the caller's environment, $`v`$ has the callee's result
  type, the callee's post holds, and every named fact under
  $`\Box_{\Phi[\sigma]}`$ at the call holds at the exit with the result named
  by a name no fact mentions (proved: `call_rule`, from `Post.rename` and
  `named_set`). The note's rule states the normal exit only; a frame crosses
  the callee's throw under its exceptional effect, $`\top`$ unless stated
  (proved: `invocation_throw_action`).
- **Alloc.** The allocated array is fresh against the heap it is allocated
  in, of length 0, and apart from every value whose store is below that heap's
  length and lists only cells below it (proved: `alloc_post`; the cells
  premise from typing, `alloc_apart_typed`). "Well-formed arrays in scope" is
  that cells premise. The separations are facts of the state after the
  allocation: freshness of $`x`$ does not keep them, a change of $`x`$'s store
  alone at $`\mathsf{any}`$ making it list $`y`$'s cell (false as a modal
  consequence of $`\mathrm{fresh}(x)`$: `apart_not_kept_fresh`); a growth of
  $`x`$'s store keeps them (proved: `apart_grow_keep`,
  `apart_grow_keep_typed`).
- **Seq-Eff.** The inclusion $`\Phi\cup\Psi'\sqsubseteq\Phi`$ is
  $`\Phi\cup\Psi'\le_{cl}\Phi`$ with the class evidence $`cl`$ holding at the
  entry heap (proved: `seq_eff`, from `action_compose_at`). Rebasing keeps each
  entry's change exactly (proved: `rebaseAll_labels`). What it cannot place,
  element cells and regions at an unlinked position, it widens to every
  location, not to their class (proved: `rebase_elems`): a cell may hold a
  store in the model, so widening to the value class needs class evidence for
  the cells (not formalized).
- **Fresh-Eff.** An entry $`x.\mathsf{store}:\delta`$ of a step's effect, with
  $`x`$'s store at or past $`b`$, covers no location below $`b`$: the step is
  within the rest of its effect there (proved: `fresh_eff`), so a closed bound
  from the invocation's entry heap survives it (proved: `fresh_eff_bound`).
  The rule erases the store only: a fresh store may list old cells, and a
  change of them is a change of the entry heap (proved:
  `fresh_cells_not_erased`).

## Transfer and the worked loop

- **Transfer** is stated as one theorem per exit (`transfer`) and composed
  into graph safety (`graph_safe`); the worked loop
  `for (j = from; j < to; j++) out[j] = xs[j]` is one instance with no premise
  about its nodes (proved: `loop_safe`, with `loop_done`: it returns `null`;
  `loop_no_raise`: it raises nothing). Its entry assertion is

  ```math
  0\le \mathit{from}\ \wedge\ \mathit{to}\le|\mathit{xs}|\ \wedge\ \mathit{xs},\ \mathit{out}\ \text{arrays of source values}
  ```

  where an array of source values is an object whose store field's location
  has the contract of a store every listed cell of which holds source values
  (`arrayF`); a state with $`\mathit{xs}=\mathit{out}`$ meets it at every
  positive budget (proved: `alias_entry`, `alias_loop_safe`).
- **Row 3, the read $`\mathit{xs}[j]`$**, needs no bound: an index at a
  hole or past the end reads `undefined` (proved: `read_safe`, from a number
  in $`j`$'s slot and $`\mathit{xs}`$ an array of source values).
- **Row 4, the write $`\mathit{out}[j]=v`$**, needs its index a valid array
  index, $`0\le j<2^{32}-1`$, which
  $`j<\mathit{to}\le|\mathit{xs}|\le 2^{32}-1`$ gives, and the written value a
  source value, which the read's result is; the note lists only the facts the
  write keeps (proved: `write_safe`, `loop_checked`).
- **Row 6, the back edge** renames the head's facts and carries the world
  facts on $`\mathit{xs}`$ and $`\mathit{out}`$ unchanged: being an array of
  source values is invariant (proved: `arrAt_invariant`).
