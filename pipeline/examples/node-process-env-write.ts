// `runRoot` records its directory in the environment, for the processes it
// forks: a write of a key `process.env` may not hold, visible through every
// alias of it. The model has no representation of a shared host object's key
// addition, so `env` is read through a readonly view and the write is
// refused where it is written (SOURCE-CONTRACTS.md, "Node's `process`").
export function remember(directory: string): void {
  process.env["TSCERT_RUN_ROOT"] = directory;
}
