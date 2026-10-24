// A `map` callback whose only program call is one typed `never` at its
// instance: the call never returns normally, so on normal return it changes
// nothing, the callback is within the empty footprint and the result is
// dense. The call is a class member's, a generic function's instance at
// `never`, and a function's with a rest parameter, none of whose signatures
// states an effect a `map` callback could use.
export class Gate {
  prefix: string = "";
  fail(message: string): never {
    throw new Error(this.prefix + message);
  }
}

export function members(gate: Gate, xs: string[]): string[] {
  const r: string[] = xs.map((x) => {
    if (x === "") return gate.fail("empty");
    return x;
  });
  return r;
}

function die<T>(message: string): T {
  throw new Error(message);
}

export function instances(xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    if (x < 0) return die<never>("negative");
    return x;
  });
  return r;
}

function failAll(...parts: string[]): never {
  throw new Error(parts.join(" "));
}

export function rests(xs: string[]): string[] {
  const r: string[] = xs.map((x) => {
    if (x === "") return failAll("empty", "string");
    return x;
  });
  return r;
}

// An async function and an async arrow whose bodies reach no completion: a
// call of the never-returning `stop`, then a throw. An async call returns
// its promise where its body throws, so each verifies at the footprint
// letting every location change, as every async definition does.
export async function rejected(
  xs: number[],
  stop: (xs: number[]) => never,
): Promise<number> {
  stop(xs);
  throw new Error("unreached");
}

export function rejecting(): (
  xs: number[],
  stop: (xs: number[]) => never,
) => Promise<number> {
  return async (
    ys: number[],
    stop: (ys: number[]) => never,
  ): Promise<number> => {
    stop(ys);
    throw new Error("unreached");
  };
}

// An async recursive constant whose body reaches no completion: it calls
// itself, then the never-returning `stop`, then throws. It verifies at the
// footprint letting every location change.
export const countdown = async (
  n: number,
  stop: (n: number) => never,
): Promise<number> => {
  if (n > 0) countdown(n - 1, stop);
  stop(n);
  throw new Error("unreached");
};
