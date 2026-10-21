// An enum a declaration file declares is the environment's object, its
// members alone assumed: no reverse key is read.
import { Tier } from "@fixture/grades-ambient";

export function tierName(t: Tier): string {
  const name: string = Tier[t] ?? "";
  return name;
}
