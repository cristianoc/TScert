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
// A signature's result `Modifies<P, T>` states the signature's frame: on a
// normal return, and on a throw where `onThrow: true` is written, every
// previously allocated location keeps its contents but those `P` names,
// each changed at most as `P` says: `values` the locations holding a value
// (`init` only those holding `null` or `undefined`, `scalar` only those
// holding neither an object nor a spine), `spines` those holding an array
// spine (`extend` only by appending fresh cells at its end), and a quoted
// location key (`"x.f"`, `"x[*]"`, `"x.*"`, `"cell(b)"`)
// the locations it names (SOURCE-ELABORATION.md, "Stated effects"). As a
// type it is `T`; the verifier certifies the statement from the definition's
// code. `Fresh<T>` states that a normal return's value holds an array spine
// the call allocated; as a type it is `T`.
type Modifies<
  P extends {
    values?: "keep" | "init" | "scalar" | "extend" | "grow" | "any";
    spines?: "keep" | "init" | "scalar" | "extend" | "grow" | "any";
    views?: "keep" | "init" | "scalar" | "extend" | "grow" | "any";
    onThrow?: true;
    [location: string]:
      | "keep"
      | "init"
      | "scalar"
      | "extend"
      | "grow"
      | "any"
      | {
          values?: "keep" | "init" | "scalar" | "extend" | "grow" | "any";
          spines?: "keep" | "init" | "scalar" | "extend" | "grow" | "any";
        }
      | true
      | undefined;
  },
  T,
> = T;
type Fresh<T> = T;
// `SafeInt` is the safe integers: the numbers whose value is an integer of
// magnitude at most 2^53 - 1, both zeros included. TypeScript reads it as
// `number`; the verifier reads it as a type of its own, the clause `int`
// (POSITIVE-TYPES.md, "The safe integers").
type SafeInt = number;
// `Dense<T>` marks an array type as having no holes (`presence: "dense"`):
// every index below its length holds a present element. TypeScript reads it as
// `T`; the verifier certifies density at every producer and uses it for
// in-bounds writes that leave the spine unchanged.
type Dense<T> = T;
