// The claims assembly stage: the importer's claims document with the claims
// of each module its qualified reads need, directly or through a module's
// reads, as its `modules`. The documents are spliced as text, so a bigint
// literal's digits pass through unrounded.

import { textCodec, type InProcessCall } from "./in-process-execution.mts";

/** The raw proposal `proposal` with `modules`, in order, as its modules. */
export function assembleClaims(proposal: string, modules: readonly string[]): string {
  const marker = '"modules":[]';
  const at = proposal.lastIndexOf(marker);
  if (at < 0) throw Error("the producer's claims state no modules");
  return proposal.slice(0, at) + `"modules":[${modules.join(",")}]` + proposal.slice(at + marker.length);
}

/** The assembly stage of `proposal` with `modules`, in order. */
export function assemblyCall(proposal: string, modules: readonly string[]): InProcessCall<string> {
  return {
    stage: "assemble",
    codec: textCodec,
    inputs: [{ role: "proposal", bytes: proposal }, ...modules.map((text, i) => ({ role: `module-${i}`, bytes: text }))],
    run: () => assembleClaims(proposal, modules),
  };
}
