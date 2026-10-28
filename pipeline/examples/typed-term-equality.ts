// Two terms of a recursive tagged union compared kind by kind, each field
// its type states, a position left out; a tag that is data of one key by its
// JSON text. The comparison type-term.mts#sameTerm makes of index contracts.
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
type Mark = (
  | { readonly guards: { readonly param: number } }
  | { readonly asserts: { readonly param: number } }
) & { readonly [key: string]: JsonValue };
type Term =
  | { k: "atom"; name: string; span: [number, number] }
  | { k: "union"; parts: Term[]; span: [number, number] }
  | {
      k: "function";
      mark: Mark | null;
      params: Term[];
      result: Term;
      rest?: Term;
    };

function sameTerms(a: readonly Term[], b: readonly Term[]): boolean {
  return (
    a.length === b.length &&
    a.every((x, i) => {
      const y = b[i];
      return y !== undefined && sameTerm(x, y);
    })
  );
}

function sameOptional(a: Term | null, b: Term | null): boolean {
  return a === null || b === null ? a === b : sameTerm(a, b);
}

export function sameTerm(a: Term, b: Term): boolean {
  switch (a.k) {
    case "atom":
      return b.k === "atom" && a.name === b.name;
    case "union":
      return b.k === "union" && sameTerms(a.parts, b.parts);
    case "function":
      return (
        b.k === "function" &&
        sameTerms(a.params, b.params) &&
        sameTerm(a.result, b.result) &&
        sameOptional(a.rest ?? null, b.rest ?? null) &&
        (a.mark === null || b.mark === null
          ? a.mark === b.mark
          : JSON.stringify(a.mark) === JSON.stringify(b.mark))
      );
  }
}
