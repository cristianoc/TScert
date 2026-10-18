// A client function stating the host's branded string as its result would
// introduce one from a plain string: refused (reading rule 5).
import type { Path } from "@fixture/host";

export function forged(): Path {
  return "plain" as Path;
}
