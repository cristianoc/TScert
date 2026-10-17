// Member accesses of values whose type admits `null` or `undefined`: where
// the value is one of those, JavaScript throws a `TypeError` before the
// access, an outcome; elsewhere the member is read at the other values' type.
type Box = { n: number; tags: string[] };

export function lastLines(ps: string[]): string[] {
  return ps.length > 1 ? ps[ps.length - 1].split("\n") : [];
}

export function trimEnd(out: string[]): string[] {
  while (out.length && !out[out.length - 1].trim()) out.pop();
  return out;
}

export function size(b: Box | undefined): number {
  // @ts-expect-error The box may be absent: the read throws there.
  return b.n;
}

export function upper(s: string | null): string {
  // @ts-expect-error The string may be null: the call throws there.
  return s.toUpperCase();
}

export function tagAt(b: Box | undefined, i: number): string | undefined {
  // @ts-expect-error The box may be absent: the read throws there.
  return b.tags[i];
}

export function appended(entries: [string, string][], s: string): string {
  entries[entries.length - 1][1] += s;
  return entries.map((e) => e[1]).join(",");
}

export function caught(b: Box | undefined): number {
  try {
    // @ts-expect-error The box may be absent: the read throws there.
    return b.n;
  } catch {
    return -1;
  }
}

export function startsBlank(lines: string[]): boolean {
  return /^\s/.test(lines[0]);
}
