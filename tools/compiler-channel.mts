/* Part of the trusted front end: the compiler's synchronous API, opened and
 * released in one place, and the one place that reads the pinned package's
 * private shape (typescript 7.0.2, `dist/api/sync/client.js`): an `API`'s
 * `client`, whose members `requestMembers` lists carry every request to the
 * compiler process, whose `close` ends that process without a request,
 * and whose `channel.child` is the process. A package that renames one of
 * them fails here, by name (`tests/tool-failures.mts` opens one).
 *
 * Every request's failure, whatever it raised (a reply the compiler sent as
 * an error, a panic, a transport or native I/O failure, a stack exhaustion
 * before or after the request was written), is thrown as a `CompilerFailure`,
 * so a catch elsewhere cannot read it as a refusal (`toolFailureOf`); a
 * failure of a file-system query the front end answered for it is thrown as
 * that query's `IoFailure`. */
import { userInfo } from "node:os";
import type { JsonObject } from "./calculus.mts";
import { join } from "node:path";
import { API, type APIOptions, type LSPConnectionOptions } from "typescript/unstable/sync";
import type { UpdateSnapshotParams } from "typescript/unstable/proto";
import { compilerFileSystem, compilerOverlay, findPackage, importLedger, installed, moduleLocation, newLedger, privateLauncher, takeQueryFailure, treeDigest, unobservable,
  withLedger, type Ledger } from "./files.mts";
import { CompilerFailure, messageOf, toolFailureOf } from "./thrown.mts";
import { compilerEnding, compilerStarted } from "./compiler-processes.mts";
import { checkedPrivateClient, guardClientRequests, type CompilerProcess, type PrivateClient } from "./client-prototype.mts";
export { heldSnapshots, queryTelemetry } from "./client-prototype.mts";

/** An API's private client, checked at the compiler-package boundary. */
export function privateClient(api: API): PrivateClient {
  return checkedPrivateClient(api);
}

/** Each client's ledger (docs/STAGE-STORE.md, "Shared work"): every
 * answer its compiler was given over its lifetime. Before each request the
 * ledger is noted in every record being made that does not hold it, and the
 * request runs with the ledger kept, so a record using the compiler holds
 * every answer its state was computed from. */
const ledgers = new WeakMap<object, Ledger>();
/** The ledger of a compiler. */
export function compilerLedger(api: API): Ledger {
  const ledger = ledgers.get(privateClient(api));
  if (!ledger) throw Error("a compiler without a ledger");
  return ledger;
}

/** Each request of a client prototype guarded once: what it throws becomes a
 * `CompilerFailure` naming the request. */
function guard(api: API): void {
  // A request is named by its method, the first argument of the API's two;
  // the others by their member.
  guardClientRequests(api, (member, receiver, args, send) => {
    const named = member === "apiRequest" || member === "apiRequestBinary";
    takeQueryFailure();
    try {
      const ledger = receiver && typeof receiver === "object" ? ledgers.get(receiver) : undefined;
      if (!ledger) return send();
      importLedger(ledger);
      withLedger(ledger, send);
    } catch (error) {
      // A file-system query the front end answered failed: that failure.
      const query = takeQueryFailure();
      if (query !== null) throw query;
      throw error instanceof CompilerFailure ? error : new CompilerFailure(named ? String(args[0]) : member, error);
    }
  });
}

/** The documents each compiler holds open, with how many times each was
 * opened: every snapshot request of an API goes through `openCompiler`'s
 * wrapper, which counts the files it opens and closes. */
const documents = new WeakMap<API, Map<string, number>>();
/** The documents `api` holds open. */
export const openDocuments = (api: API): string[] => [...(documents.get(api)?.keys() ?? [])];
const documentKey = (document: unknown): string => typeof document === "string" ? document : String(JSON.stringify(document));

/** A compiler process opened through the API, its requests guarded and the
 * documents it holds open counted. */
export function openCompiler(options: APIOptions | LSPConnectionOptions | undefined): API {
  let api: API;
  try {
    api = new API(options);
  } catch (error) {
    throw new CompilerFailure("spawn", error);
  }
  const client = privateClient(api);
  guard(api);
  const open = new Map<string, number>();
  documents.set(api, open);
  const request = api.updateSnapshot.bind(api);
  Object.assign(api, { updateSnapshot: (params?: UpdateSnapshotParams) => {
    const snapshot = request(params);
    for (const document of params?.openFiles ?? []) open.set(documentKey(document), (open.get(documentKey(document)) ?? 0) + 1);
    for (const document of params?.closeFiles ?? []) {
      const key = documentKey(document), count = (open.get(key) ?? 0) - 1;
      if (count > 0) open.set(key, count);
      else open.delete(key);
    }
    return snapshot;
  } });
  compilerStarted(client.channel.child.pid);
  return api;
}

/* The front end's compiler (STAGE-STORE.md, "Observed stages"): every file-system
 * query the API delegates is answered by `files.mts`, and the process runs
 * where it can read no other file of the user's. */

/** The installation the front end loads, the package `typescript` its own
 * `node_modules` holds (or a test's, `useInstallationForTests`), and its
 * executable, the platform package's `lib/tsc` as the package's
 * `getExePath` finds it: real paths, or why there is none. */
type Installation = { package: string; executablePackage: string; executable: string; missing?: never } | { missing: string };
function locate(from: string): Installation {
  const at = findPackage("typescript", from);
  if (at === null) return { missing: `the package typescript is not installed for ${from}` };
  const platformPackage = findPackage(`@typescript/typescript-${process.platform}-${process.arch}`, at);
  if (platformPackage === null) return { missing: `typescript has no executable for ${process.platform}-${process.arch}` };
  const executable = join(platformPackage, "lib", "tsc");
  return installed(executable) ? { package: at, executablePackage: platformPackage, executable }
    : { missing: `${executable} is not installed` };
}

/** The sandbox profile of the compiler installed in `executablePackage`,
 * launched by `launcher` in the empty directory `directory`: any read or
 * existence test of a path outside the system volume, the installation, the
 * launcher and the directory kills it, but three probes of system libraries,
 * which are denied. The sandbox matches a path as it is named: each of the
 * three is allowed under its real path and under the system's own link to
 * it (`/var`, `/tmp` and `/etc` link into `/private`). */
const quote = (path: string): string => `"${path.replace(/[\\"]/g, (c) => `\\${c}`)}"`;
const named = (path: string): string[] => [...new Set([path, path.replace(/^\/private\/(var|tmp|etc)\//, "/$1/")])];
function profile(executablePackage: string, launcher: string, directory: string, home: string): string {
  const probes = `(literal ${quote(join(home, ".CFUserTextEncoding"))}) (subpath "/AppleInternal") ` +
    `(subpath "/Library/Preferences/Logging")`;
  const own = [...named(executablePackage).map((p) => `(subpath ${quote(p)})`),
    ...[launcher, directory].flatMap(named).map((p) => `(literal ${quote(p)})`)].join(" ");
  return [
    "(version 1)",
    "(allow default)",
    "(deny file-read* file-test-existence",
    "  (require-not (require-any",
    `    (literal "/") (literal "/var") (literal "/tmp") (literal "/etc") (subpath "/System") (subpath "/usr/lib") (subpath "/dev")`,
    `    ${probes}`,
    `    ${own}))`,
    "  (with send-signal SIGKILL))",
    `(deny file-read* file-test-existence (regex #"^/System/Volumes/Data/") (with send-signal SIGKILL))`,
    `(deny file-read* file-test-existence ${probes})`,
  ].join("\n");
}
const shellQuoted = (text: string): string => `'${text.replace(/'/g, `'\\''`)}'`;
/** The case sensitivity of the executable's file system, as the compiler
 * probes it: whether the executable's path with each letter's case swapped
 * names nothing. */
const swapCase = (text: string): string =>
  [...text].map((c) => c === c.toUpperCase() ? c.toLowerCase() : c.toUpperCase()).join("");

/** The compiler's identity, captured when this module loads: its
 * installation's files, its executable's path, its file system's case
 * sensitivity and its sandbox profile (with the process's own paths left
 * out), and whether it differs from disk now; or why the compiler's reads
 * are not all observed. */
export type CompilerImplementation =
  { identity: { [field: string]: string | boolean }; changed: () => boolean; unobserved?: never } | { unobserved: string; identity?: never };
type Identification = { identity: { [field: string]: string | boolean }; unobserved?: never } | { unobserved: string; identity?: never };
function identify(at: Installation): Identification & JsonObject {
  if (at.missing !== undefined) return { unobserved: at.missing };
  if (process.platform !== "darwin" || !installed("/usr/bin/sandbox-exec"))
    return { unobserved: "the compiler's own reads are confined on macOS only (sandbox-exec)" };
  const packageDigest = treeDigest(at.package), executableDigest = treeDigest(at.executablePackage);
  if (packageDigest === null || executableDigest === null) return { unobserved: "the compiler's installation is missing" };
  return { identity: { executable: at.executable, packagePath: at.package, package: packageDigest, executablePackage: executableDigest,
    caseSensitive: !installed(swapCase(at.executable)),
    profile: profile(at.executablePackage, "<launcher>", "<directory>", userInfo().homedir) } };
}
/** The installation in use, its implementation and its launcher. */
type Current = { installation: Installation; implementation: CompilerImplementation; launcher: string | null };
function current(from: string): Current {
  const installation = locate(from);
  const data = identify(installation);
  const identified: Identification = data;
  return { installation, launcher: null, implementation: identified.unobserved !== undefined ? identified
    : { identity: identified.identity,
      changed: (): boolean => JSON.stringify(identify(locate(from))) !== JSON.stringify(data) } };
}
let using: Current = current(moduleLocation(import.meta.dirname));
/** How many times the installation in use was chosen: a compiler opened
 * under one choice is not another's. */
let choices: number = 0;
/** The compiler's implementation, as this process loaded it. */
export const compilerImplementation = (): CompilerImplementation => using.implementation;
/** The compiler's identity as a retained session compares it
 * (`declaration-session.mts`): the installation's choice and identity. */
export const compilerChoice = (): string =>
  JSON.stringify([choices, using.implementation.identity !== undefined ? using.implementation.identity : using.implementation.unobserved]);
/** Tests only: the compiler installed in the `node_modules` of `directory`
 * from now on, or the front end's own for null. */
export function useInstallationForTests(directory: string | null): void {
  using = current(directory ?? moduleLocation(import.meta.dirname));
  choices++;
}

/** The launcher of the confined compiler, made once per installation. */
function launcher(): string | null {
  const { installation, implementation } = using;
  if (implementation.unobserved !== undefined || installation.missing !== undefined) return null;
  const { executable, executablePackage } = installation;
  using.launcher ??= privateLauncher((directory, script) => [
    "#!/bin/sh",
    `cd ${shellQuoted(directory)} || exit 70`,
    `exec /usr/bin/env -i PWD=${shellQuoted(directory)} /usr/bin/sandbox-exec -p ${
      shellQuoted(profile(executablePackage, script, directory, userInfo().homedir))} ${shellQuoted(executable)} "$@"`,
    "",
  ].join("\n")).launcher;
  return using.launcher;
}
/** Tests only: the launcher of the confined compiler, or null. */
export const launcherForTests = (): string | null => launcher();

/** The front end's compiler, its working directory `cwd`: the texts of
 * `overlay` at their paths, every other file-system query an observation,
 * and, where it can be, the process confined to them. */
export function openFrontEndCompiler(cwd: string, overlay: Map<string, string>, ledger: Ledger = newLedger()): API {
  const confined = launcher();
  const { installation, implementation } = using;
  if (confined === null && implementation.unobserved !== undefined) unobservable(implementation.unobserved);
  const api = openCompiler({ cwd, fs: compilerFileSystem(compilerOverlay(overlay), installation.missing !== undefined ? null : installation.executablePackage),
    ...(confined ? { tsserverPath: confined } : {}) });
  ledgers.set(privateClient(api), ledger);
  return api;
}

/** The compiler process of an API, for a test that waits for its end. */
export const compilerProcess = (api: API): CompilerProcess => privateClient(api).channel.child;

/** A compiler process about to end, announced to its observer
 * (`compiler-processes.mts`). */
const observeEnd = (api: API): void => compilerEnding(privateClient(api).channel.child.pid);

/** Ends the compiler process without a request: the client closes its
 * channel's pipes and signals the process, then the process is killed,
 * which it cannot ignore. */
export function abandonCompiler(api: API): void {
  observeEnd(api);
  abandon(api);
}
function abandon(api: API): void {
  const client = privateClient(api);
  try {
    client.close();
  } finally {
    const child = client.channel.child;
    if (child.exitCode === null && child.signalCode === null) child.kill("SIGKILL");
  }
}

/** Releases a compiler after its work, or after `thrown`. Where the channel
 * is readable (no failure, a refusal, a panic the compiler replied), it is
 * closed in order: its snapshots released by request, then its process
 * ended. Where it may not be (any other tool failure), it is abandoned,
 * without a further request. A failure closing it abandons it and is
 * reported, as a tool failure, with what was in flight as context. */
export function releaseCompiler(api: API, thrown: { error: unknown } | null): void {
  const failure = thrown && toolFailureOf(thrown.error);
  if (failure && !failure.readable) {
    observeEnd(api);
    abandon(api);
    return;
  }
  // The process's end is announced as the API closes its channel, after the
  // requests releasing its snapshots, so their work is observed.
  const client = privateClient(api);
  const closeChannel = client.close;
  Object.assign(client, { close: function (this: unknown): void {
    observeEnd(api);
    closeChannel.call(this);
  } });
  try {
    api.close();
  } catch (error) {
    observeEnd(api);
    abandon(api);
    const context = thrown ? `, closing the compiler after: ${messageOf(thrown.error).split("\n")[0] ?? ""}` :
      ", closing the compiler";
    throw new CompilerFailure("close", error, context);
  }
}
