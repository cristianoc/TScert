// Census: fragment-parse.mts#parseFile, #parseFragment, #lowerModule,
// #lowerModuleText, #parseModules, #lowerFile.
// A local closure collects rest arguments and infers its result.
export function names(): number {
  const add = (...names: string[]) => names.length;
  return add("one");
}

export function collect(): number {
  let count = 0;
  const add = (...names: string[]) => {
    count += names.length;
  };
  add("one", "two");
  add();
  return count;
}

export function prefixed(): number {
  const add = (prefix: number = 1, ...names: string[]) => prefix + names.length;
  return add(undefined, "one");
}
