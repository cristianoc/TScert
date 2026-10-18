// A callback taking a callback taking the branded string: the client calls
// the inner one, producing the brand (reading rule 5).
import { nested } from "@fixture/host";

export function run(): void {
  nested((each) => each("plain"));
}
