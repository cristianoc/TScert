// PAPER: the effect language's declarations (docs/drafts/effect-languages.md): a
// footprint, and the bound `AtMost<P>` of an effect variable, whose argument has no
// type meaning (docs/SOURCE-CONTRACTS.md, "Arguments without type meaning").
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
