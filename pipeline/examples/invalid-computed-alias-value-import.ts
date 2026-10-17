// An imported computed alias is exactly the keys TypeScript computes: a key
// of the union is no value of one member's keys.
import type { KeysOf } from "@fixture/lib";
type Step = { bind: number } | { branch: string };
export function only(k: KeysOf<Step>): "bind" {
  return k;
}
