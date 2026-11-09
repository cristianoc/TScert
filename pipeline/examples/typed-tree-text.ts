// A tree's canonical text written kind by kind, its spans aside (the pattern
// of `termText`, `named-record.mts`): `JSON.stringify` serializes only
// strings and numbers, and the recursion is the program's own code, so a
// `map` calling it stays dense.
type Span = [start: number, end: number];
type Term =
  | { k: "atom"; name: string; span: Span }
  | { k: "index"; at: number; span: Span }
  | { k: "union"; parts: Term[]; span: Span }
  | { k: "array"; readonly: boolean; element: Term; span: Span };

function text(t: Term): Modifies<{}, string> {
  const k = `{"k":${JSON.stringify(t.k)}`;
  switch (t.k) {
    case "atom":
      return `${k},"name":${JSON.stringify(t.name)}}`;
    case "index":
      return `${k},"at":${JSON.stringify(t.at)}}`;
    case "union":
      return `${k},"parts":[${t.parts.map(text).join(",")}]}`;
    case "array":
      return `${k},"readonly":${JSON.stringify(t.readonly)},"element":${text(t.element)}}`;
  }
}

export function keys(ts: readonly Term[]): string[] {
  return ts.map((t) => text(t));
}
