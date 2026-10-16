// A `RegExp` annotation is the conservative structural regex: every capture
// may be unmatched, a split is a readonly view, and a literal of any shape
// meets it, stored in records and arrays as expected-diagnostic patterns are.
type Expectation = { file: string; diagnostic: RegExp };

export const expectations: Expectation[] = [
  { file: "a", diagnostic: /no derivation of (its|the) claim/ },
  { file: "b", diagnostic: /^(\w+)=(.*)$/m },
];

export function matches(detail: string, e: Expectation): boolean {
  return e.diagnostic.test(detail);
}

export function key(re: RegExp, line: string): string {
  const m = re.exec(line);
  if (!m) return "";
  const k = m[1];
  return k !== undefined ? k : m[0];
}

export function pieces(re: RegExp, s: string): readonly (string | undefined)[] {
  return s.split(re);
}

export function clean(re: RegExp, s: string): string {
  return s.replace(re, "");
}

export function check(s: string): string {
  return key(/(\w+):/, s) + clean(/\s/g, s) + String(pieces(/,/, s).length);
}
