// PAPER: the effect language's declarations (docs/drafts/effect-languages.md): a
// footprint, the bound `AtMost<P>` of an effect variable, `Effects<P, T>` for
// paper-checked effects (including confined module state `@state`), and
// `Join<E, P>` for joining an effect variable with a closed anchored effect,
// whose arguments have no type meaning (docs/SOURCE-CONTRACTS.md, "Arguments
// without type meaning").
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type Effects<P extends Footprint, T> = T;
type Join<E extends Footprint, P extends Footprint> = Footprint;
