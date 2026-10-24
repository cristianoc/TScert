// The verifier's own declarations a program writes. The parser recognizes
// each by its declaration here, which TypeScript binds the name to, never by
// its spelling.
//
// `T extends Resolvable` makes `T` resolvable, owning its observation and
// result, and `T extends Awaitable` makes it awaitable, owning its
// observation only (SOURCE-CONTRACTS.md, "Implied bounds"). As a type each is
// `unknown`: a qualification constrains which instances a call may take, not
// the values of `T`.
type Resolvable = unknown;
type Awaitable = unknown;
// A signature's result `Within<F, T>` states the signature's effect: on a
// normal return, and on a throw where `onThrow` is written, the call changes
// the previously allocated locations holding a value (`value`) and those
// holding an array store (`store`) at most as `F` says (SOURCE-ELABORATION.md,
// "Stated effects"). As a type it is `T`; the verifier certifies the
// statement from the definition's code.
type Footprint = {
  value: "keep" | "any";
  store: "keep" | "grow" | "any";
  onThrow?: true;
};
type Within<F extends Footprint, T> = T;
