// `pipeline/host-fixture/` names the host package and its reviewed version in
// its manifest, and is no installation of it: its declarations get no host
// reading, so `jsDoc` is an ordinary member here. Read as the host package
// (pipeline/test.mts, through the test-only stand-in), the same read is
// refused.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  return n.jsDoc;
}
