// A union of host nodes and false keeps false as a possible && result.
import type { Node } from "typescript/unstable/ast";

type Receiver = Node | false;

export function signature(receiver: Receiver): string {
  return receiver && "printed";
}
