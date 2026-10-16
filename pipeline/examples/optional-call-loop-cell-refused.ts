// An optional call through a `let` the loop assigns: the receiver is an
// array where the call runs, but the producer finds no arrow to call.
export function collect(lines: string[], into: string[]): number {
  let target: string[] | undefined;
  for (const line of lines) {
    target?.push(line);
    target = into;
  }
  return into.length;
}
