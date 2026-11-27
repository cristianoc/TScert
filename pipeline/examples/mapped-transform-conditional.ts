// Per-key value-transforming mapped types with sound TypeTerm-level conditional
// `infer` on generic class/interface references, constant-value homomorphic
// mapped types over named interfaces and indexed records, and standalone
// distributive conditional `infer`.
declare class AbstractInput {
  readonly __brand: undefined;
}
declare class InputDef<K, V> extends AbstractInput {
  readonly initial: readonly [K, readonly V[]][];
  constructor(initial: readonly [K, readonly V[]][]);
}
interface EagerCol<K, V> {
  readonly key: K;
  readonly val: V;
}

type InputCols<Defs> = {
  readonly [K in keyof Defs]: Defs[K] extends InputDef<infer Key, infer Val>
    ? EagerCol<Key, Val>
    : never;
};
type AllInputs<T> = { readonly [K in keyof T]: AbstractInput };
type UnwrapInputVal<T> = T extends InputDef<infer _K, infer V> ? V : never;

interface NamedDefs {
  readonly names: InputDef<string, number>;
  readonly count: number;
}

export function readNamed(
  cols: InputCols<NamedDefs>,
  defs: AllInputs<{ readonly a: InputDef<string, string> }>,
  emptyDefs: AllInputs<Record<string, never>>,
  unwrapped: UnwrapInputVal<InputDef<string, boolean> | number>,
): number {
  const _a: AbstractInput = defs.a;
  const _e: AbstractInput | undefined = emptyDefs["k"];
  const _u: boolean = unwrapped;
  return (
    cols.names.val +
    cols.names.key.length +
    (_u ? 1 : 0) +
    (_a.__brand === undefined ? 0 : 1) +
    (_e === undefined ? 0 : 1)
  );
}
