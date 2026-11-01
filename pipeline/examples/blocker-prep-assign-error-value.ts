// Census functions:
// files.mts#realPath
// files.mts#listDirectory
export function absent(what: string): Error {
  return Object.assign(Error(`ENOENT: no such ${what}`), { code: "ENOENT" });
}

export function coded(what: string, cause: unknown): Error & { code: string } {
  return Object.assign(new Error(what, { cause }), { code: "ENOENT" });
}
