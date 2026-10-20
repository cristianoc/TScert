// A call of a function declared to return `never` returns normally into no
// environment: after `if (…) fail(…)` the next statement is reached by the
// condition's `false` edge alone, and sees its refinement. A call returning
// a value continues as any call does.
function fail(message: string): never {
  throw new Error(message);
}

function warn(message: string): void {
  if (message.length > 1000) throw new Error("long");
}

export function checked(x: string | number): string {
  if (typeof x !== "string") fail("not a string");
  return x;
}

export function bound(x: string | number): string {
  const never = typeof x === "string" ? x : fail("not a string");
  return never;
}

// The statement after the call is reached by no edge: its bindings are
// claimed at the empty type.
export function unreached(x: number): number {
  fail("always");
  return x;
}

// The call's throw still reaches the handler and the `finally` block: only
// its normal return is never taken.
export function caught(x: string | number): string {
  let seen = "start";
  try {
    if (typeof x !== "string") fail("not a string");
    seen = x;
  } catch {
    seen = typeof x === "number" ? "caught" : "thrown";
  } finally {
    seen = seen + "!";
  }
  return seen;
}

export function warned(x: string | number): string {
  if (typeof x !== "string") warn("not a string");
  return typeof x === "string" ? x : "";
}
