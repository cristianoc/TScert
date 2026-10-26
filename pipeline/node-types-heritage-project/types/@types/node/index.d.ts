// Node's declarations as a variant would write them: `StatSyncFn` names
// its reviewed call signature exactly, and extends an interface stating a
// further member.
declare module "fs" {
  type PathLike = string;
  interface Stats {
    size: number;
  }
  interface Promisified {
    __promisify__(path: string): Promise<Stats>;
  }
  export interface StatSyncFn extends Promisified {
    (path: PathLike, options?: undefined): Stats;
  }
  export const statSync: StatSyncFn;
}
declare module "node:fs" {
  export * from "fs";
}
