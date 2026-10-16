// A fresh object literal's own keys are exactly the ones it writes: it lacks
// the optional field it leaves out, and has no prototype.
interface Options {
  readonly port: number;
  readonly cors?: boolean;
}

function portOf(options: Options): number {
  return options.port;
}

export function run(): number {
  return portOf({ port: 3587 });
}
