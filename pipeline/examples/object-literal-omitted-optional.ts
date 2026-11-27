// An object literal omitting an optional property establishes that reading
// that omitted property yields `undefined`, discharging `@invariant` and
// `@ensures` clauses guarded by `x.items === undefined` as well as direct
// reads of the omitted property.
type Items = {
  extras: number[] | null;
  tags: number[];
};

/** @invariant this.items === undefined || this.items.extras === null || this.widths.length <= this.items.extras.length
 *  @invariant this.items === undefined || this.items.tags.length === this.widths.length
 */
type Data = {
  widths: number[];
  items?: Items;
};

export function makeWithoutItems(widths: number[]): Data {
  const result: Data = { widths };
  return result;
}

/** @ensures result.items === undefined || result.widths.length === 0 */
export function makeEnsuresOmitted(widths: number[]): Data {
  const result: Data = { widths };
  return result;
}

export function makeJoinedWithoutItems(widths: number[], flag: boolean): Data {
  const result: Data = flag ? { widths } : { widths };
  return result;
}

export function readOmittedOptional(widths: number[]): undefined {
  const obj: Data = { widths };
  return obj.items;
}

export function useData(d: Data): number {
  if (d.items === undefined) return d.widths.length;
  if (d.items.extras === null) return d.items.tags.length;
  if (d.widths.length === 0) return 0;
  return d.items.extras[0]!;
}
