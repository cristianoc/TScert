// Regular expression literals: `test`, `exec` with captures that always take
// part read as strings, `match`, `search`, `split`, `replace` with a string
// replacement, and `matchAll` iterated and spread, under each flag.
const WORD = /^[a-z]+$/i;

export function word(s: string): boolean {
  return WORD.test(s) && /\w/u.test(s) && /^a.b$/s.test(s) && /^x$/m.test(s);
}

// Both groups take part in every match: `m[1]` and `m[2]` are strings.
export function assignment(line: string): [string, string] | null {
  const m = /^(\w+)=(.*)$/.exec(line);
  return m ? [m[1], m[2]] : null;
}

// Group 1 sits under an alternative: it may be unmatched, and is tested.
export function digits(line: string): string {
  const m = /(\d+)|-/.exec(line);
  return m ? (m[1] ?? "none") : "";
}

export function width(line: string): number {
  return /^ */.exec(line)?.[0].length ?? 0;
}

export function escape(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/`([^`]+)`/g, "<code>$1</code>");
}

// No group: every piece is a string.
export function words(s: string): string[] {
  return s.split(/\s+/).filter((w) => w.length > 0);
}

export function position(s: string): number {
  return s.search(/[A-Z]/y) + s.search(/b/d);
}

export function firstMatch(s: string): string {
  const all = s.match(/\d/g);
  const one = s.match(/(x)y/);
  return (all ? all[0] : "") + (one ? one[1] : "");
}

export function tokens(code: string): string {
  const token = /([a-z]+)|(\d+)/g;
  let out = "";
  for (const m of code.matchAll(token)) {
    const [t, name] = m;
    out += name !== undefined ? `<w>${t}</w>` : `${t}@${m.index}`;
  }
  return out;
}

export function count(code: string): number {
  return [...code.matchAll(/\d/g)].length;
}
