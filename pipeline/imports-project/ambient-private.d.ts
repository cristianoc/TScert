// An external declaration file whose class has an unannotated `private` field
// (as `tsc --declaration` emits for private constructor parameter properties)
// and an untyped public field.
declare module "@fixture/ambient-private" {
  export class ServiceInstance {
    private readonly refs;
    pub;
    getName(): string;
  }
}
