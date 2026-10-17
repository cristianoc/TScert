// An imported alias TypeScript computes from its parameter, as a local one:
// each application is the union of literals TypeScript computes for it, in a
// parameter and as a mapped type's keys.
import type { KeysOf } from "@fixture/lib";
type Step = { bind: number } | { branch: string };
const SHOW: { [K in KeysOf<Step>]: string } = { bind: "→", branch: "if" };
export function show(k: KeysOf<Step>): string {
  return `${k} ${SHOW[k]}`;
}
