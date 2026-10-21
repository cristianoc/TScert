// An enum a declaration file declares: the environment's object, its members
// alone assumed (`invalid-enum-reverse-declared-value-import`).
declare module "@fixture/grades-ambient" {
  export enum Tier {
    Low = 1,
    High = 2,
  }
}
