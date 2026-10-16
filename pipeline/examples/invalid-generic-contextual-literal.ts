// Only a fresh literal is claimed at its exact keys: a record held in a
// variable may carry further keys its type does not name, `verbose` at any
// type among them, so it is not an `Options`. TypeScript accepts it.
interface Options {
  readonly port: number;
  readonly verbose?: boolean;
}

function run<T>(value: T, _options: Options): T {
  return value;
}

export function start(settings: { readonly port: number }): number {
  return run(1, settings);
}
