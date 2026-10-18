// The branded string where the host produces it, in a union, an optional
// member and three levels of callbacks: read as a string (reading rule 5).
import { maybe, nestedOut, type Located } from "@fixture/host";

export function lengths(l: Located): number {
  const m = maybe();
  const a = l.alternative;
  let total =
    (m === undefined ? 0 : m.length) + (a === undefined ? 0 : a.length);
  nestedOut((each: (take: (path: string) => void) => void) =>
    each((path: string) => {
      total = total + path.length;
    }),
  );
  return total;
}
