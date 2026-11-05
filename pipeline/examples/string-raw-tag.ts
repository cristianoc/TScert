// `String.raw` as a template tag, through the reviewed overlay: the
// template of the source's raw strings, each substitution a primitive
// converted by ToString between them (run under Node).
export const mark: string = String.raw`^\p{M}$`;

export function joined(
  n: number,
  s: string,
  u: string | undefined,
  b: boolean,
  big: bigint,
): string {
  return String.raw`n=${n}\t${s}\n${u}|${b}|${big}`;
}

// Escapes a cooked template refuses or reads otherwise: an invalid Unicode
// escape, an escaped backtick and `${`, a line continuation, the empty one.
export function escapes(): string[] {
  return [
    String.raw`\u{`,
    String.raw`\``,
    String.raw`\${x}`,
    String.raw`a\
b`,
    String.raw``,
  ];
}

function push(log: string[], value: string): string {
  log.push(value);
  return value;
}

// Substitutions run in order, each value taken where it runs.
export function ordered(log: string[]): string {
  let n = 1;
  return String.raw`${push(log, "a")}${n}-${push(log, "b")}${(n = 2)}${n}`;
}
