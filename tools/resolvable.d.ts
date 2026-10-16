// The verifier's own declarations a program writes to qualify a type
// parameter (SOURCE-CONTRACTS.md, "Implied bounds"): `T extends Resolvable`
// makes `T` resolvable, owning its observation and result, and
// `T extends Awaitable` makes it awaitable, owning its observation only. The
// parser recognizes each bound by its declaration here, which TypeScript
// binds the name to, never by its spelling. As a type each is `unknown`: a
// qualification constrains which instances a call may take, not the values
// of `T`.
type Resolvable = unknown;
type Awaitable = unknown;
