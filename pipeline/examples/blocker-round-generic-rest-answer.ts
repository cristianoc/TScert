// Census functions: declaration-graph.mts#declarationAnswer,
// declaration-graph.mts#declarationServices, declaration-graph.mts#collectDeclarations.
interface Options {
  answer?: (value: string) => string;
}
export function deliver(options: Options, value: string): string | undefined {
  const service: Pick<Options, "answer"> = options;
  return service.answer?.(value);
}
export function evaluate(
  options: Options,
  value: () => string,
): string | undefined {
  const service: Pick<Options, "answer"> = options;
  return service.answer?.(value());
}
