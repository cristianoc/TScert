// Re-exports are module declarations: the host links them before the module
// runs, after their modules have run, so the initialization runs nothing for
// them, and the module's own code is checked as it is without them.
export { double as twice, limit } from "@fixture/lib";
export * as library from "@fixture/lib";
export * from "@fixture/relay";

export function quadruple(x: number): number {
  return x * 4;
}
