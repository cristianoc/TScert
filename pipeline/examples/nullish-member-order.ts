// The order JavaScript evaluates a member access of `null` or `undefined`
// in: a computed key first, then the throw; a method call throws before its
// actuals; a compound assignment reads the old value, throwing, before its
// right side. An optional chain skips its key where its receiver is nullish,
// and a member of its result is an ordinary access.
type Box = { n: number; tags: string[] };

function key(log: string[]): "n" {
  log.push("key");
  return "n";
}

function amount(log: string[]): number {
  log.push("rhs");
  return 1;
}

function start(log: string[]): number {
  log.push("arg");
  return 0;
}

export function keyFirst(b: Box | undefined, log: string[]): number {
  // @ts-expect-error The box may be absent: the read throws there.
  return b[key(log)];
}

export function argumentsSkipped(s: string | null, log: string[]): string {
  // @ts-expect-error The string may be null: the call throws there.
  return s.slice(start(log));
}

export function bumped(b: Box | undefined, log: string[]): number {
  // @ts-expect-error The box may be absent: the update throws there.
  b[key(log)] += amount(log);
  return log.length;
}

export function optionalKey(
  b: Box | undefined,
  log: string[],
): number | undefined {
  return b?.[key(log)];
}

export function chained(b: Box | undefined): number {
  // @ts-expect-error The chain may be undefined: the read throws there.
  return (b?.tags).length;
}
