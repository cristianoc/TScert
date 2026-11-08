# Element ownership: keeping quantified facts across writes into the same array

Status of this design: deferred (owner, 2026-11-08). Pretext's code does not
need it: every array written in place whose elements serve as indices is a
typed array, whose distinct indices are distinct bytes of its buffer, and the
ordinary index arrays (`itemSegments`, `starts`) are only pushed. Writes to
other, freshly allocated arrays are covered by freshness. This design is kept
for code that writes into an ordinary array a quantified fact constrains; for
such code, rewriting it (building the array by `push`, or a typed array) may
be the better engineering than this invariant's cost (estimated 18–30 days of
Lean work, below).

## The existing mechanism this extends

This proposal extends the footprint mechanism's fact/stability/checked-contract rule ([FOOTPRINTS.md:30](../FOOTPRINTS.md), element writes at :327), the frame conditions of [PROGRAM-TYPING.md:1725](../PROGRAM-TYPING.md), and its quantified clauses (:2614). The operational owner is [SEMANTICS.md:10](../SEMANTICS.md); its array invariant (:964) concerns types, prototypes and keys. **The proposed element ownership invariant is an additional semantic obligation.** All proposed preservation results below require proofs.

Paths below are relative to `the repository`; `pretext/` means `the pretext bounds target`. Line citations describe the inspected checkout.

The existing bounded-write rule preserves lengths (`lean/Verification/Programs/IndexWrites.lean:1205`, `lengthOutput`; :1217, `boundedLength_sound`). General filtering rejects `every` and `element` (`lean/Verification/Semantics/IndexFacts.lean:1289`). The branch also contains the approved push extension (`docs/PROGRAM-TYPING.md:2676`, `lean/Verification/Programs/PromiseCalls.lean:1943`, :1975). The new rule belongs beside those rules; it uses the existing quantified body, linear entailment, alias classes and separation knowledge.

## Ownership of admissible heaps

Let S be the ordinary store cells, E the current element cells, and O the other observable cells: object fields (including stores and prototype links), identity cells, binding/reference cells and host/typed-array metadata. Include cells observable through environments, captures, results and exceptions, not just heap-resident objects. Write L_s for the list in store s and define:

```math
\mathrm{Own}_h(s,i,\ell)\iff s\in S\land h(s)=\mathsf{arr}(L_s)\land L_s[i]=\mathsf{some}(\ell).
```

The proposed invariant is:

```math
\begin{aligned}
E&=\{\ell\mid\exists s,i.\ \mathrm{Own}_h(s,i,\ell)\},\\
\forall\ell\in E.\quad &\exists! (s,i).\ \mathrm{Own}_h(s,i,\ell),\\
E\cap O&=\varnothing,\qquad S\subseteq O,\\
\forall\ell\in E.\quad &\ell<|h|\land\mathrm{SourceValue}(h(\ell)).
\end{aligned}
```

Thus two positions of one store and positions of distinct stores have distinct cells. Aliases of one array share its store. Elements may contain the same object value, including an object containing that array; uniqueness concerns storage cells, not stored object identities. Deleted cells can remain allocated without a current owner. Holes have no element cell.

**Admissibility needs a configuration judgment as well as this heap predicate.** A temporary `arr` value must carry provenance for its owner or for a fresh, uninstalled store. Allocation reserves distinct cells; installation transfers those reservations to the new store. Reading a store produces a view of that owner. Writing back its updated view preserves the owner. Copying an array reads values and allocates new element cells; copying an array-valued field copies the array reference. No source operation may install one store list under a second independent store owner.

This is essential for `arrAlloc`, which returns a list before a store cell exists, and `setGrow`, which returns an updated list before `writeField` installs it (`lean/Verification/Semantics/Calculus.lean:2021`, :2044, :1997). A heap-only theorem for arbitrary `Step` is false: arbitrary term operands can contain a duplicated location list or install an existing list into a second store. The proof target is preservation by **admissible source configurations and admissible external contracts**, with well-formed temporary store views. Ghost ownership/provenance changes the proof model; present writes retain their operational behavior.

`HeapOk` currently checks contracts independently at each location (`lean/Verification/Semantics/Heaps.lean:17`); `write_sound` explicitly permits aliases (:52). It does not imply ownership. Introduce a separate `OwnedHeap` and configuration admissibility, then thread their conjunction with `HeapOk` through safety, call contracts and the exported acceptance theorem. Ownership must survive truncation of the step index and world extension, and every claimed allocation extension must establish it. Arbitrary appended values need not preserve it.

## Preservation obligations: complete heap-step inventory

The direct heap-changing constructors of `Step` are the following seven. All citations in this table are to `lean/Verification/Semantics/Calculus.lean`.

| Rule | Required ownership lemma |
| --- | --- |
| `makeFields`, :1963 | Fresh field/identity cells; source-valued fields retain valid object references. A store initializer is installed from its matching reservation, once. |
| `writeField`, :1997 | An ordinary field write stores an admissible source value. A store-field write installs only that owner's updated view, releasing deleted positions and registering fresh positions. |
| `arrAlloc`, :2021 | `elemSlots` reserves pairwise distinct fresh cells, apart from every observable cell and existing owner. |
| `arrAllocThrow`, :2025 | Fresh error identity cell is outside E; no uninstalled array escapes. |
| `setPresent`, :2039 | The view names its owner; changing its unique element cell to a source value preserves ownership and every other position. |
| `setGrow`, :2044 | Fresh element cell and `placeAt` preserve uniqueness, including holes, sparse extension and maximum-index cases; eventual installation has the same owner. |
| `arithThrow`, :2059 | Fresh error identity cell is outside E. |

The evaluation-context constructors inherit the inner step's proof: `callL` :1925, `callRecv` :1927, `callArg` :1928, `constructL` :1935, `constructArg` :1936, `letC` :1939, `spreadC` :1947, `makeArg` :1958, `readC` :1966, `indexC1/C2` :1980/:1981, `writeC1/C2` :1995/:1996, `testC` :2000, `iteC` :2003, `arithC1/C2` :2006/:2007, `arrArg` :2011, `elemC1/C2` :2027/:2028, `setC1/C2/C3` :2034/:2035/:2036, `lenC` :2047, `throwC` :2057, `mergeC1/C2` :2061/:2062, `makeKeyC1/C2` :2068/:2069, `frameC` :2090. Every other constructor leaves the heap unchanged but must preserve configuration provenance.

Specific nonlocal obligations:

| Boundary | Proof/audit required |
| --- | --- |
| Spread, merge, computed fields | `arrSpread` :2016 reads values before fresh allocation; `mergeV` :2065 and `makeKeyV` :2072 reduce to `makeFields`. `Programs/ObjectMerge.lean:201` proves `mergeParts_store`: object copying excludes the store key. Prove copied fields cannot expose element cells as field locations. |
| Calls, constructors, rest arguments, captures | `callBound` :1943, `callSpread` :1948, `constructSpread` :1953, `callGraph` :2079, `constructGraph` :2084, `gotoEnter` :2088, and frame return/bind/handler rules :2092–2118 transfer provenance across values and environments; rest allocation uses the same fresh-element lemma. |
| Native array mutations | `Semantics/FootprintNatives.lean:39` (`Arr.set`), :43 (`delete`), :46 (`setLength`): prove ownership preservation for these primitives, then `push` :173, `pop` :176, `shift` :181, `unshiftMoves` :190 and `unshift` :196, `reverse` :201, sort `writeback` :213. Moves copy values into destination cells. Callback effects in sort must also preserve ownership. |
| Native heap guarantee | `FootprintNatives.lean:390` and :407 (`array_native_post`, `_any`) take heap-side premises. Add ownership preservation to the audited native contract: the existing footprint alone cannot prove it. The module header :5–16 identifies this trust boundary. |
| Other native operations and copies | Audit every admitted contract, including fill/copyWithin/splice, length changes, slice/concat/map/filter, Array construction/from/of and filled-array intrinsics where admitted. Fresh results require fresh element cells even when values are shared; callbacks, rejection and exceptional returns preserve admissibility. These are contract obligations, not additional `Step` constructors in this calculus. |
| External inputs/results | Require one coherent ownership representation for the whole input heap, preserving aliases across parameters, fields, globals and callbacks. Apply it to imported functions, native returns and thrown values. `Semantics/Safety.lean:68` (`Safe`) must propagate it; callable semantics must quantify over admissible futures. `Source/Claims/Json.lean:577` (`checkUnitJson_safe`) must expose the strengthened premise through `UnitSafe`. Document the host correspondence in `docs/SEMANTICS.md:1058` and the trust surface. |

## Rule for `xs[k] = v`

Reuse `boundedSlots` and the writable homogeneous store check (`Programs/IndexWrites.lean:1118`, :1137). Operands are evaluated first. On their resulting state require:

1. Admissibility, ordinary write typing, a source-valued element contract, and a decoded array index with `0 <= k && k < xs.length`. This rule covers replacement and a hole filled below the length; extension at the old length remains a separate case.
2. For each candidate `every(y.p,t,B)`, preserve its array path, bound t, and **every free body term** across the entire element-write/store-write sequence. Use proved ownership disjointness plus existing footprint/separation checks. A lexical root difference is insufficient.
3. Establish either that the candidate's store is the receiver's, or that the two stores are apart. Existing alias/separation evidence supplies this decision; unresolved candidates are dropped.
4. For the same store, prove the body at k with its element replaced by v, whenever k lies in the quantified range. If the body uses the element numerically, establish `safeInteger(v)` and all substituted inequalities by existing linear entailment. Evaluate free terms in the post-state, or prove their pre/post equality first.

For a fixed, preserved bound n, the semantic lemma is:

```math
\frac{\mathrm{every}(xs,n,B)_h\quad 0\le k<|xs|\quad
 \mathrm{Owned}(h)\quad\mathrm{frame}(n,\mathrm{free}(B))\quad
 (k<n\Rightarrow B(k,v)_{h'})}
 {\mathrm{every}(xs,n,B)_{h'}}.
```

The proof splits an arbitrary index i into i=k and i≠k. Ownership supplies the latter's unchanged element cell; the substitution premise supplies the former. For an apart store, every element is unchanged. For full-array facts n=|xs|, the strict bounded write preserves n. An existing element-dependent fact also supplies presence at every index in its range; a hole cannot satisfy that premise. A hole write can still preserve facts over other arrays.

Use the i≠k assertion internally in the proof. Export a whole-array `every` only after the k obligation succeeds. Persisting a punctured quantifier for later statements would require a separate fact syntax and edge rule; it is outside this draft. Repeated writes that each meet B need no such syntax.

Implementation: add `every_written`/`every_apart_write` in `IndexFacts.lean`, a checked replacement-body substitution beside `PromiseCalls.appendedBody` (:2029), candidate filtering in `HeapKnowledge.lean` beside `keptIndices` (:1598), and the postcondition in `IndexWrites.lean` beside `boundedLength_sound`. Keep generic `keptBy` conservative. Preserve slot shifting, guarded facts, read bridges and edge entailment; `HeapKnowledge.every_follows` (:338) remains the edge mechanism.

## Composition with push

`ReceiverGrows` preserves the old location-list prefix and every other old cell (`Semantics/CallEffects.lean:273`). `ReceiverAppends` relates new positions to actual values (:283); **it does not assert fresh or distinct new locations**. Admissibility must supply that obligation for the trusted push contract. A native witness that appends the same location twice can satisfy a value relation but violate ownership.

Reuse `every_grown`, `every_appended`, `appendedBody` and `appendKept` (`Programs/PromiseCalls.lean:1943`, :1975, :2029, :2054). Push can retain an inequality bounded above by a growing length; an element replacement uses preserved lengths and exact replacement substitution. A builder can alternate a proved append and a bounded replacement, checking B each time. The branch's single-actual restriction remains (`docs/PROGRAM-TYPING.md:2702`). Ownership preservation also applies to multi-actual native push, even when quantified extension is not supported.

## Pretext: exact proposed annotations and limits

These are proposed source annotations, not claims that the full functions verify. Loop tags attach immediately before the indicated loop (`docs/PROGRAM-TYPING.md:2753`). No pretext file is edited.

**`setEmptyObjectFacts`**, `pretext/src/rich-inline.ts:735`, writing `spaces[first]` at :777, needs the item-index facts to survive writes to the fresh `spaces` array. Proposed entry clauses:

```ts
/**
 * @requires items.length + 1 <= itemSegments.length
 * @requires starts.length == items.length
 * @requires data.segmentFlags.length <= data.widths.length
 * @requires data.segmentFlags.length <= data.segments.length
 * @requires data.segmentFlags.length <= segmentItems.length
 * @requires forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= data.segmentFlags.length
 */
```

Repeat the last clause as `@invariant` before the reverse item loop (:760). The bound is inclusive: the final entry is the end sentinel. Establishing `first < count` after `first !== end` additionally needs `first <= end`; the current single-element body cannot express `itemSegments[i] <= itemSegments[i+1]` (`tools/bound-annotations.mts:293`). An ordering contract/rule or a checked local bound is a separate requirement. The `isSoftHyphenSegment` requirements are at `rich-inline.ts:693`. The typed-array write to `returns` (:779) needs its own frame guarantee. This proposal alone does not certify this function.

**`getExtraSpacings`**, `pretext/src/measurement.ts:679`, writes ordinary `extras[i]` at :706. Its relevant loop annotations are:

```ts
/**
 * @invariant safeInteger(count) && 0 <= count && count <= ends.length
 * @invariant extras.length == 0 || extras.length == count
 */
```

Place them before :691's loop. The ordinary write requires `i < count`, plus the `zeros(count)` length guarantee. The invariant must survive the `Map.set` and Canvas calls too. The `ends` buffer is an `Int32Array`, and its initialized-prefix contract belongs to `findGraphemeEnds` (`pretext/src/graphemes.ts:64`). There is no justified requirement that all `extras` values are safe integers: `Math.round` alone proves neither finiteness nor the safe range of external Canvas widths. This function motivates bounded writes and length preservation; it does not itself require an ordinary-array numeric quantified body.

**`countLigaturesOnFirstLetter`**, `pretext/src/measurement.ts:1280`, writes `advances[first]` and `advances[i]` at :1290–1291. Proposed entry and loop clauses:

```ts
/** @requires advances.length <= ends.length */
// Before the for loop at :1286:
/** @invariant safeInteger(first) && 0 <= first && first < i */
```

The loop guard supplies `i < advances.length`; the invariant supplies the first write's bound. `advances` holds fractional widths, so `forall i in advances: safeInteger(advances[i])` is invalid. Bounds on `ends`' string offsets require a typed-array content contract; ordinary-array ownership does not supply it. Calls to measurement helpers require appropriate frames.

**Builders**, `pretext/src/rich-inline.ts:338`, :581: before the containing item loop and the final sentinel loop, respectively:

```ts
/** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= widths.length */
/** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= segmentCount */
```

The fast-path builder (:217) uses:

```ts
/** @invariant forall i in itemSegments: safeInteger(itemSegments[i]) && 0 <= itemSegments[i] && itemSegments[i] <= data.segmentFlags.length */
```

Push establishes each new element; ownership framing retains these facts across bounded writes to widths and other separately allocated ordinary arrays (:459–575). The `starts` builder (:253) can carry `@invariant forall i in starts: safeInteger(starts[i]) && 0 <= starts[i] && starts[i] <= source.length`; growth of the string value needs its own arithmetic proof at reassignment.

For `zeros` (`pretext/src/measurement.ts:650`), use entry `@requires safeInteger(count) && 0 <= count && count <= 4294967295`, and before its loop:

```ts
/** @invariant out.length == i */
/** @invariant forall j in out: safeInteger(out[j]) && out[j] == 0 */
```

Its callable result contract must state length=count and every element=0. `zeroList` (`rich-inline.ts:861`) needs the same result contract, a zero-element invariant on its shared `ZEROS` cache, and a slice contract copying values into fresh cells. The existing body-fact machinery can describe zero elements; exporting that guarantee and proving the copy are separate obligations. Arrays initialized by `new Array(...).fill(null)` (:531–532) need density and fresh-cell ownership, not a numeric safe-integer annotation on null elements.

## Cases and Node negatives

Positive pipeline cases: replacement satisfying B; two successive writes; preservation at a distinct position; same-store aliases with valid replacement; two fresh arrays; array read through a field with proved store separation; holes below length for an unrelated quantified fact; copied array with shared object values but distinct cells; push/write/push builder; the pretext sentinel shape. Include source-independent forged-certificate controls for missing ownership, duplicate locations in one store, shared locations between stores, an element cell reused as a field cell, and missing body/frame premises.

Each unsafe source negative must fail the verifier and execute under Node with the violated claim observed:

| Negative | Minimal witness (B is safe integer and nonnegative) |
| --- | --- |
| Alias write | `const xs=[0]; const ys=xs; ys[0]=-1;` then require `xs[0]>=0`. |
| Write at k breaks B | `const xs=[0,1]; xs[1]=-1;` then require `xs[1]>=0`. An accepted body proof at index 0 proves nothing at index 1. |
| Array through another field | `const a=[0]; const p={left:a,right:a}; p.left[0]=-1;` then require `p.right[0]>=0`. Field-name inequality supplies no store separation. |
| Free body term changes | `const xs=[1]; const box={limit:1}; box.limit=0;` then require `xs[0]<=box.limit`. Framing the array alone is insufficient. |
| Copied references share objects | `const a=[{n:0}]; const b=a.slice(); b[0].n=-1;` then require `a[0].n>=0`. This tests the ownership boundary; nested-element predicates need their own syntax. |

Add a forged native append witness reusing an old element cell and a malformed external input with duplicate owners. These are semantic controls, not Node programs: ordinary JavaScript cannot expose element storage cells. Node negatives are planned tests, not executions performed for this draft.

## Cost and risks

Estimates are engineering judgment in focused person-days, including proofs and local checks; they are not measured build times.

| Lean area | Estimate | Deliverable |
| --- | --- | --- |
| New ownership module; `Calculus`, `Heaps`, `ObjectCoherence` | 5–8 | Heap/configuration invariant, allocation reservations, seven direct-step lemmas and context induction. |
| `Safety`, `HeapObservations`, `OperationWorlds`, `Rules`, allocation/call/type semantics, `GraphCode`, source acceptance | 6–10 | Admissible-future quantification and propagation through safety and all boundaries. |
| `FootprintNatives`, `CallEffects`, copy/native contracts | 3–5 | Mutator composition, fresh-copy guarantee, normal/exception/callback audits, push compatibility. |
| `IndexFacts`, `HeapKnowledge`, `IndexWrites`, `PromiseCalls` | 3–5 | Semantic replacement/frame lemmas, checked entailment and output knowledge. |
| Checker wiring and Lean controls | 1–2 | Forged facts/heaps refused; existing soundness/axiom checks pass. |

Lean total: **18–30 days**. Producer propagation, source cases, Node negatives, native audits and documentation add approximately **3–5 days**. Separate ordering, typed-array and result-contract work needed by pretext is outside that estimate. Validate narrowly while developing, then Lean build, axiom controls, full `make test` and documentation checks (`CLAUDE.md:73`, :316).

The main risk is the foundational scope: existing semantic types admit arbitrary contract-satisfying heaps, including aliased cells. Strengthening only the bounded-write theorem leaves calls and input heaps unsound. A second risk is transient store duplication: a proof over heap lists alone misses values in terms and captures. A third is host fidelity: shallow copies share element values while owning distinct cells, and native callbacks can mutate aliases. Frame proofs must track paths and free terms as well as element ownership.

Route (a), this proposal, retains in-place present writes and pays the global admissibility proof cost. Route (b), allocating a fresh element cell on every bounded write, changes `setPresent`'s operational model and requires a host correspondence proof. Route (c), element-region separation facts, can frame separate regions but by itself supplies no within-store uniqueness for i≠k. The first implementation milestone is the admissible-configuration preservation theorem; quantified preservation depends on that theorem, not on an unchecked ownership premise added locally.
