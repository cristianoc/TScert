// A data intersection is an obligation on an existing object too.
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };
type Data = { readonly [key: string]: Json };
export function encode(value: { n: number }): string {
  const data: Data & { n: number } = value;
  return JSON.stringify(data);
}
