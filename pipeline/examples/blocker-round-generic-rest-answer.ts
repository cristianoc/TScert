// Census functions: declaration-graph.mts#declarationAnswer,
// declaration-graph.mts#declarationServices, declaration-graph.mts#collectDeclarations.
interface Options { answer?: (value: string) => string }
function captured<A extends readonly unknown[], R>(options: Options,
  answer: ((...args: A) => R) | undefined): ((...args: A) => R) | undefined {
  return answer == null ? undefined : (...args: A): R => Reflect.apply(answer, options, args);
}
export function deliver(options: Options, value: string): string | undefined {
  const service = { get answer() { return captured(options, options.answer); } };
  return service.answer?.(value);
}
