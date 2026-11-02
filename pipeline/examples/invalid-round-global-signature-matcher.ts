// A falsely promised matcher shrinks find's captured range and exposes undefined.
import type {
  GlobalEntry,
  GlobalSignatureMatcher,
} from "../../tools/library-globals.mts";
export function lookup(): GlobalEntry | undefined {
  const entries: GlobalEntry[] = [
    {
      global: "X",
      signature: "first",
      host: { k: "transparent", why: "test" },
    },
    {
      global: "X",
      signature: "second",
      host: { k: "transparent", why: "test" },
    },
  ];
  const context: { matches: GlobalSignatureMatcher } = {
    matches: (_signature) => {
      entries.pop();
      return false;
    },
  };
  return entries.find(
    (e) =>
      e.global === "X" &&
      e.member === undefined &&
      context.matches(e.signature) &&
      (e.origin ?? "library") === "library",
  );
}
