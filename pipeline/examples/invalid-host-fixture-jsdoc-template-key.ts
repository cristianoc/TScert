// A template with a substitution evaluating to "jsDoc": refused.
import type { Node } from "@fixture/host";

export function docs(n: Node, suffix: "Doc"): unknown {
  return n[`js${suffix}`];
}
