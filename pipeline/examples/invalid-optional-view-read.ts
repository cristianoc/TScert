// A readonly optional field may be absent: its read is not a number.
interface Config {
  readonly limit?: number;
}
export function limitOf(config: Config): number {
  return config.limit;
}
