// A hook chain declared as Node's `module.registerHooks` declares its own
// (`mapped-named-hook-value-import`): the next hook takes a `Partial` of the
// context interface the declaration names.
declare module "@fixture/hooks-ambient" {
  interface HookContext {
    conditions: string[];
    parentURL: string | undefined;
  }
  interface HookOutput {
    url: string;
  }
  export type NextResolve = (
    specifier: string,
    context?: Partial<HookContext>,
  ) => HookOutput;
  export function resolveThrough(
    specifier: string,
    hook: (
      specifier: string,
      context: HookContext,
      next: NextResolve,
    ) => HookOutput,
  ): HookOutput;
}
// A declaration taking `Partial` of an interface with a call signature
// (`mapped-named-call-refused-value-import`), which the reader refuses.
declare module "@fixture/hooks-ambient-callable" {
  interface Ticker {
    (): void;
    count: number;
  }
  export function tick(ticker: Partial<Ticker>): number;
}
