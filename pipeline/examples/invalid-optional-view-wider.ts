// A readonly optional field of a wider type may hold a string: it does not
// cover a readonly optional number.
interface Config {
  readonly limit?: number;
}
function limitOf(config: Config): number | undefined {
  return config.limit;
}
export function pass(value: {
  readonly limit?: number | string;
}): number | undefined {
  return limitOf(value);
}
