// A class instance lacking the key has a prototype, where a read of the key
// would continue: it does not establish the readonly optional field.
// (TypeScript accepts this.)
interface Config {
  readonly limit?: number;
  readonly name: string;
}
function limitOf(config: Config): number | undefined {
  return config.limit;
}
class Plain implements Config {
  readonly name: string = "plain";
}
export function pass(): number | undefined {
  return limitOf(new Plain());
}
