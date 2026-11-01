// files.mts#entriesRead,#entriesOf,#compilerFileSystem and
// family-activation.mts#activeGuards,#loadedGuards,#activateGuards,
// #checkedGuards,#guardOfExport serialize named records as JSON dictionaries.
// Retain the full key contract when constructing a record and across returns.
type Entries = {
  readonly [key: string]: readonly string[];
  files: readonly string[];
  directories: readonly string[];
};

export function entries(
  files: readonly string[],
  directories: readonly string[],
): Entries {
  return { files, directories };
}

export function encoded(
  files: readonly string[],
  directories: readonly string[],
): string {
  const listed = entries(files, directories);
  return JSON.stringify(listed);
}

type Closure = {
  readonly [key: string]:
    | Readonly<Record<string, string>>
    | readonly (readonly [string, string])[];
  files: Readonly<Record<string, string>>;
  edges: readonly (readonly [string, string])[];
};

export function closure(
  files: Readonly<Record<string, string>>,
  edges: readonly (readonly [string, string])[],
): Closure {
  return { files, edges };
}

export function encodedClosure(
  files: Readonly<Record<string, string>>,
  edges: readonly (readonly [string, string])[],
): string {
  return JSON.stringify(closure(files, edges));
}
