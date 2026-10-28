// Projection follows the imported alias to its interface declaration.
import type { Shape } from "../imports-project/computed-index-chain.js";
export function x(at: Shape["at"]): number {
  return at[0];
}
