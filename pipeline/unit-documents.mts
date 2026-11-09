// The documents the pipeline and the producer exchange to propose a document
// a unit at a time (`unit-slices.mts`, `verify-source.mts`). Each is written
// or read once, as declared here; `tests/json-field-names.mts` compares these
// names with the producer's reads and writes.

/** What `producer --units` prints of a document: per function name, the
 * module functions its code mentions and whether it mentions a name the
 * initialization declares; the initialization's mentions; the constants the
 * document reads as values. */
export type UnitFacts = {
  /** Module bindings whose objects escape in the complete document. */
  escaped: string[];
  functions: { name: string; mentions: string[]; init: boolean; names: string[] }[];
  init: { mentions: string[]; names: string[] } | null;
  readAsValues: string[];
};

/** A function a unit reads, at the footprint (none where it proposes none)
 * and on-throw flag its own unit's proposal settled on: one line of what
 * `producer --unit` prints, and an entry of a reads document. */
export type Interface = { name: string; footprint: unknown; thrown: boolean };

/** A qualified read as the producer reads it. */
export type QualifiedEntry = { local: string; declaration: unknown; footprint: unknown; onThrow: boolean };

/** A unit's reads document: its members, whether the initialization is one,
 * the functions it reads, the constants read as values, its qualified reads. */
export type UnitReads = {
  members: string[];
  init: boolean;
  pinned: Interface[];
  readAsValues: string[];
  qualified: QualifiedEntry[];
};

/** An entry of an assembly: the intervals the slice leaves out, and each
 * slice symbol's index in the document. */
export type AssemblyEntry = { deletions: [number, number][]; symbols: number[] };

/** A slice's claims document where the producer refuses the functions the
 * slice holds by their signatures (`producer --unit`): the refusal, which
 * the unit's search states (`verifier --produce-unit`). */
export type SliceClaimsRefusal = { refusal: string };
