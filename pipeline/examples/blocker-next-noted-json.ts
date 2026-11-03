// Census: tools/files.mts#nodeResolve,#resolveObserved.
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | JsonObject;
type JsonObject = { readonly [key: string]: JsonValue };

type Observation = readonly [string, string, string | null];
type Noted = { observation: Observation; node: boolean } & JsonObject;
export function same(before: Noted[], after: Noted[]): boolean {
  return JSON.stringify(before) === JSON.stringify(after);
}
