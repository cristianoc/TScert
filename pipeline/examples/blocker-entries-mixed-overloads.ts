// `Object.entries` of a recursive data union's dictionary arm, its entries
// filtered and mapped through written tuple patterns: each entry keeps the
// union's contract, so the printer recurses on it.
type ContractData =
  | null
  | undefined
  | boolean
  | number
  | string
  | readonly ContractData[]
  | { readonly [key: string]: ContractData };
const isArrayData = (value: ContractData): value is readonly ContractData[] =>
  Array.isArray(value);
export function canonical(value: ContractData): string {
  if (Array.isArray(value)) {
    // Both tests are the same pure native operation.
    if (!isArrayData(value)) throw Error("array data tests disagree");
    const items: readonly ContractData[] = value;
    return `[${items.map(canonical).join(",")}]`;
  }
  if (value !== null && typeof value === "object")
    return `{${Object.entries(value)
      .filter(([key]: [string, ContractData]) => key !== "span")
      .map(
        ([key, field]: [string, ContractData]) => `${key}:${canonical(field)}`,
      )
      .join(",")}}`;
  return typeof value === "string" ? JSON.stringify(value) : String(value);
}
