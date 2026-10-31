// Census: fragment-parse.mts#parseFile, #parseFragment, #lowerModule,
// #lowerModuleText, #parseModules, #lowerFile.
// A local closure collects rest arguments and infers its result.
export function names(): number {
  const add = (...names: string[]) => names.length;
  return add("one");
}
