/* Part of the trusted front end: every file-system operation it makes, in one
 * place. Whatever an operation throws is an `IoFailure` naming the operation
 * and the path, a tool failure by where it came from, whatever its fields
 * (Node's permission model throws ERR_ACCESS_DENIED with no `syscall`). The
 * one exception is `orAbsent`, where a path that names nothing (ENOENT, or
 * ENOTDIR for a path through a file) is an absence its caller gives a
 * meaning. */
import { readdirSync, readFileSync, realpathSync, statSync, type Dirent, type Stats } from "node:fs";
import { createRequire } from "node:module";
import { fieldOf, IoFailure } from "./thrown.mts";

/** `run`, its failure an `IoFailure` of `operation` at `path`. */
function io<T>(operation: string, path: string, run: () => T): T {
  try {
    return run();
  } catch (error) {
    throw new IoFailure(operation, path, error);
  }
}

/** A file's text, as UTF-8. */
export const readText = (path: string): string => io("read", path, () => readFileSync(path, "utf8"));
/** A file's bytes. */
export const readBytes = (path: string): Buffer => io("read", path, () => readFileSync(path));
/** A path's real path, every link resolved. */
export const realPath = (path: string): string => io("resolve", path, () => realpathSync(path));
/** A directory's entries. */
export const listDirectory = (path: string): Dirent[] => io("list", path, () => readdirSync(path, { withFileTypes: true }));
/** The file a module specifier names, resolved from `from` as Node resolves it. */
export const resolveModule = (from: string, specifier: string): string =>
  io("resolve the module", specifier, () => createRequire(from).resolve(specifier));

/** The value of one of the operations above, run as `operation`, or null
 * where its path names nothing. */
export function orAbsent<T>(operation: (path: string) => T, path: string): T | null {
  try {
    return operation(path);
  } catch (error) {
    const cause = error instanceof IoFailure ? error.cause : error;
    const code = fieldOf(cause, "code");
    if (code === "ENOENT" || code === "ENOTDIR") return null;
    throw error;
  }
}
/** A path's status. */
export const status = (path: string): Stats => io("stat", path, () => statSync(path));
