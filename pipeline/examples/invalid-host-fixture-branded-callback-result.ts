// A client callback returning the branded string would introduce one: the
// host function taking it is refused (reading rule 5, L5).
import { withPath } from "@fixture/host";

export function give(): void {
  withPath(() => "plain");
}
