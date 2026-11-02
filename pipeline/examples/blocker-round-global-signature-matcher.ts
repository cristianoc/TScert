// Census functions: library-globals.mts#globalEntry; declaration-graph.mts#globalNamespace.
// A known string matcher is retained through the owned lookup context.
import type {
  GlobalEntry,
  GlobalSignatureMatcher,
} from "../../tools/library-globals.mts";
export function lookup(text: string): GlobalEntry | undefined {
  const entries: GlobalEntry[] = [
    {
      global: "X",
      signature: "call",
      host: { k: "transparent", why: "test" },
    },
  ];
  const context: { matches: GlobalSignatureMatcher } = {
    matches: (signature) => signature === text,
  };
  return entries.find(
    (e) =>
      e.global === "X" &&
      e.member === undefined &&
      context.matches(e.signature) &&
      (e.origin ?? "library") === "library",
  );
}
