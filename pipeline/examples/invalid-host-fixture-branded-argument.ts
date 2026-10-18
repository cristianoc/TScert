// A host generic applied to the branded string: its argument's direction is
// not known, so the brand is refused (reading rule 5).
import { holder } from "@fixture/host";

export function read(): number {
  return holder().value.length;
}
