// An optional host parameter of the branded string is still one the client
// produces (reading rule 5, L5).
import { optionally } from "@fixture/host";

export function run(): void {
  optionally("plain");
}
