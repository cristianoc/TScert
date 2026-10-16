// A record without the symbol-keyed field is not branded.
import { unwrap } from "@fixture/lib";
export function forged(n: number): number {
  return unwrap({ n: n });
}
