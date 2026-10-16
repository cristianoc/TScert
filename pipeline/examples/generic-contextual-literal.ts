// A fresh literal passed to a generic function at a parameter that mentions
// none of its type parameters is built at that parameter, as at a call
// without them: it leaves out an optional field by its exact keys.
interface Options {
  readonly port: number;
  readonly verbose?: boolean;
}

function run<T>(value: T, _options: Options): T {
  return value;
}

export function start(): number {
  return run(1, { port: 8080 });
}
