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
// holding neither an object nor a store), `stores` those holding an array
// store, and a quoted location key (`"x.f"`, `"x[*]"`, `"x.*"`, `"cell(b)"`)
// the locations it names (SOURCE-ELABORATION.md, "Stated effects"). As a
// type it is `T`; the verifier certifies the statement from the definition's
// code. `Fresh<T>` states that a normal return's value holds an array store
// the call allocated; as a type it is `T`.
type Modifies<
  P extends {
    values?: "keep" | "init" | "scalar" | "grow" | "any";
    stores?: "keep" | "init" | "scalar" | "grow" | "any";
    onThrow?: true;
    [location: string]:
      | "keep"
      | "init"
      | "scalar"
      | "grow"
      | "any"
      | {
          values?: "keep" | "init" | "scalar" | "grow" | "any";
          stores?: "keep" | "init" | "scalar" | "grow" | "any";
        }
      | true
      | undefined;
  },
  T,
> = T;
type Fresh<T> = T;
