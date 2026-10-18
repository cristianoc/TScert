// A host-supplied function taking the branded string, held by the client,
// would accept a plain string: refused where it is read (reading rule 5, L5).
import { taker } from "@fixture/host";

export function call(): void {
  taker()("plain");
}
