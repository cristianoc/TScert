// A readonly optional field grants no write.
interface Config {
  readonly limit?: number;
}
export function reset(config: Config): void {
  config.limit = 0;
}
