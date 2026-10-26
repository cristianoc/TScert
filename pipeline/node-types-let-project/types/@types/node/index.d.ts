// Node's declarations as a variant would write them: `statSync` names its
// reviewed call signature exactly, through a `let`, which other code may
// assign.
declare module "fs" {
  type PathLike = string;
  interface Stats {
    size: number;
  }
  export interface StatSyncFn extends Function {
    (path: PathLike, options?: undefined): Stats;
  }
  export let statSync: StatSyncFn;
}
declare module "node:fs" {
  export * from "fs";
}
