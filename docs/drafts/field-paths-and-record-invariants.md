# Field paths and record invariants

Part of [checked bound annotations](checked-bound-annotations.md) (#115).
The design of record invariants that hold beyond the boundaries
[type invariants](../ARITHMETIC.md#type-invariants) check: across a
published record's own mutation, and of records stored in other structures.

## The existing mechanism this extends

[Type invariants](../ARITHMETIC.md#type-invariants): an `@invariant` is a
precondition of each parameter whose type names its record and a
postcondition of each result, and of each parameter its function does not
reassign, kept between boundaries by
[frame conditions](../PROGRAM-TYPING.md#frame-conditions) and
[footprints](../FOOTPRINTS.md); a sealed handle states it over its
representation's fields. A value given the record's type by a cast, a
spread, a native or a read of another structure's field carries no fact.
[Field-path terms](../ARITHMETIC.md#linear-facts) read the paths a clause
names.

## 2. Record invariants

**Proposed.** For `PreparedLineBreakData`, candidate clauses equate `widths.length`,
`breakableFitAdvances.length` and the actual typed array's length.
Nullable arrays need guarded equalities, such as
`this.lineEndTrims === null || this.lineEndTrims.length === this.widths.length`
([guarded clauses](../ARITHMETIC.md#guarded-clauses)).
An index stored beside its array may state safe integrality and strict bounds.
A cursor with an end sentinel instead permits equality at rest; a read needs
a strict branch bound. A cursor's relation to a separate record belongs
in a callable precondition unless both values share an invariant root.

**Proposed mutation discipline.** Pushing to one parallel array breaks equality
until the other append completes. Such builders use raw construction state,
then prove the invariant before publication.
For published records, temporarily opening an invariant requires an exclusive
capability covering the locations it reads and all observer aliases.
Callbacks, escaping references and exception handlers must be unable to
observe an open record as closed; restoration is required before such exposure.
That capability discipline is further design work; the first step refuses
temporary opening and checks each supported mutation while closed.

**Proposed alias rule.** `readonly` restricts writes through a reference;
it proves neither immutable array contents nor absence of writable aliases.
Persistent invariant-bearing references require checked control of all writers.
Without that control, retain the predicate as expiring point knowledge and
re-establish it at each observation boundary.
External inputs require validation or an explicit trusted contract; external
calls must account for callbacks, mutation and exceptional exits.

**Observed in source.** `segmentFlags` documents JSON copies with indexed
properties but no length. Such copies do not satisfy the typed-view predicate.
Supporting them requires a distinct indexed-record contract or validation;
a typed-array length equality covers only actual admitted typed arrays.

**Trust proposal.** Lean checks establishment, transport and consumption.
The front end remains responsible for annotation attachment, path resolution,
faithful declaration translation and signature/request agreement.
Native postconditions and external invariants require separate contract audits.
The owner reviews these trust changes and any alias-exclusion assumption;
the existing fixed-buffer view assumption does not imply record immutability.

**Records in other structures.** A record read from another record's
field, an array or a `WeakMap` carries no invariant fact: a nested
invariant of the containing structure would state it. A rich-inline item's
representation shares the paragraph's lists, which later iterations grow,
so its introduction is refused until a predicate for shared data is stated.

**An exported cursor.** A path precondition no caller's fact establishes,
an exported parameter's cursor passed to `getSegmentIndex`
(`field-path-precondition-unestablished`, pretext's
`layoutNextRichInlineLineRange`), needs an invariant of the cursor's type
or a validated entry.
