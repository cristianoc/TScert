declare function pick(value: { [key: string]: number | undefined }): number;
declare function pick(value: {
  [key: string]: number | undefined;
  narrow?: 1;
}): number;

export function optionalDictionary(value: {
  [key: string]: number | undefined;
  narrow?: 1;
}): number {
  return pick(value);
}

declare function view(value: { [key: string]: number | undefined }): number;
declare function view(value: {
  [key: string]: number | undefined;
  readonly narrow?: 1;
}): number;

export function optionalDictionaryView(value: {
  [key: string]: number | undefined;
  readonly narrow?: 1;
}): number {
  return view(value);
}
