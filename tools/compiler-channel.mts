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
import { join } from "node:path";
import { API } from "typescript/unstable/sync";
import { compilerFileSystem, findPackage, installed, privateLauncher, takeQueryFailure, treeDigest, unobservable } from "./files.mts";
import { CompilerFailure, fieldOf, messageOf, toolFailureOf } from "./thrown.mts";

/** The compiler process, as the client's channel holds it. */
interface CompilerProcess {
  readonly pid?: number;
  readonly exitCode: number | null;
  readonly signalCode: string | null;
  kill(signal: "SIGKILL"): boolean;
  once(event: "exit", listener: () => void): unknown;
}
/** The members of an `API`'s private client this module uses. */
interface PrivateClient {
  close(): void;
  readonly channel: { readonly child: CompilerProcess };
}
type Request = (this: unknown, ...args: unknown[]) => unknown;
const isRequest = (f: unknown): f is Request => typeof f === "function";
const isProcedure = (f: unknown): f is () => unknown => typeof f === "function";
/** A value's prototype, where its methods are own members. */
const prototypeOf = (value: object): unknown => Object.getPrototypeOf(value);

/** The client's members that send a request on its channel: every one of
 * them, the API's requests through the first two, and an echo and the
 * timing queries through the others. */
const requestMembers = ["apiRequest", "apiRequestBinary", "echo", "echoBinary", "getTimingInfo", "resetTimingInfo"] as const;

/** An `API`'s private client, its members checked by name. */
export function privateClient(api: API): PrivateClient {
  const client = fieldOf(api, "client");
  const missing = (member: string): Error =>
    Error(`the compiler package's private shape changed: API.client${member} is missing (compiler-channel.mts)`);
  if (!client || typeof client !== "object") throw missing("");
  if (!("close" in client) || !isProcedure(client.close)) throw missing(".close");
  for (const member of requestMembers)
    if (!isRequest(fieldOf(prototypeOf(client), member))) throw missing(`.${member}`);
  const child = fieldOf(fieldOf(client, "channel"), "child");
  if (!child || typeof child !== "object" || !("kill" in child) || !isProcedure(child.kill) ||
      !("once" in child) || !isProcedure(child.once) || !("exitCode" in child) || !("signalCode" in child))
    throw missing(".channel.child");
  return client as PrivateClient; // asserted: the decoder of the private client, each member it names checked above
}

/** Each request of a client prototype guarded once: what it throws becomes a
 * `CompilerFailure` naming the request. */
const guarded = new WeakSet<object>();
function guard(client: PrivateClient): void {
  const prototype = prototypeOf(client);
  if (!prototype || typeof prototype !== "object" || guarded.has(prototype)) return;
  // A request is named by its method, the first argument of the API's two;
  // the others by their member.
  const wrap = (member: string, original: unknown): Request => {
    if (!isRequest(original)) throw Error(`the compiler package's private shape changed: API.client.${member} (compiler-channel.mts)`);
    const named = member === "apiRequest" || member === "apiRequestBinary";
    return function (this: unknown, ...args: unknown[]): unknown {
      takeQueryFailure();
      try {
        return original.call(this, ...args);
      } catch (error) {
        // A file-system query the front end answered failed: that failure.
        const query = takeQueryFailure();
        if (query !== null) throw query;
        throw error instanceof CompilerFailure ? error : new CompilerFailure(named ? String(args[0]) : member, error);
      }
    };
  };
  Object.assign(prototype, Object.fromEntries(requestMembers.map((member) =>
    [member, wrap(member, fieldOf(prototype, member))])));
  guarded.add(prototype);
}

/** A compiler process opened through the API, its requests guarded. */
export function openCompiler(options: ConstructorParameters<typeof API>[0]): API {
  let api: API;
  try {
    api = new API(options);
  } catch (error) {
    throw new CompilerFailure("spawn", error);
  }
  guard(privateClient(api));
  return api;
}

/* The front end's compiler (DESIGN.md, "Observed stages"): every file-system
 * query the API delegates is answered by `files.mts`, and the process runs
 * where it can read no other file of the user's. */

/** The installation the front end loads, the package `typescript` its own
 * `node_modules` holds (or a test's, `useInstallationForTests`), and its
 * executable, the platform package's `lib/tsc` as the package's
 * `getExePath` finds it: real paths, or why there is none. */
type Installation = { package: string; executablePackage: string; executable: string } | { missing: string };
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
  { identity: { [field: string]: string | boolean }; changed: () => boolean } | { unobserved: string };
function identify(at: Installation): { identity: { [field: string]: string | boolean } } | { unobserved: string } {
  if ("missing" in at) return { unobserved: at.missing };
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
  const identified = identify(installation);
  return { installation, launcher: null, implementation: "unobserved" in identified ? identified
    : { identity: identified.identity,
      changed: (): boolean => JSON.stringify(identify(locate(from))) !== JSON.stringify(identified) } };
}
let using: Current = current(import.meta.dirname);
/** The compiler's implementation, as this process loaded it. */
export const compilerImplementation = (): CompilerImplementation => using.implementation;
/** Tests only: the compiler installed in the `node_modules` of `directory`
 * from now on, or the front end's own for null. */
export function useInstallationForTests(directory: string | null): void {
  using = current(directory ?? import.meta.dirname);
}

/** The launcher of the confined compiler, made once per installation. */
function launcher(): string | null {
  const { installation, implementation } = using;
  if ("unobserved" in implementation || "missing" in installation) return null;
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
export function openFrontEndCompiler(cwd: string, overlay: ReadonlyMap<string, string>): API {
  const confined = launcher();
  const { installation, implementation } = using;
  if (confined === null && "unobserved" in implementation) unobservable(implementation.unobserved);
  return openCompiler({ cwd, fs: compilerFileSystem(overlay, "missing" in installation ? null : installation.executablePackage),
    ...(confined ? { tsserverPath: confined } : {}) });
}

/** The compiler process of an API, for a test that waits for its end. */
export const compilerProcess = (api: API): CompilerProcess => privateClient(api).channel.child;

/** Ends the compiler process without a request: the client closes its
 * channel's pipes and signals the process, then the process is killed,
 * which it cannot ignore. */
export function abandonCompiler(api: API): void {
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
    abandonCompiler(api);
    return;
  }
  try {
    api.close();
  } catch (error) {
    abandonCompiler(api);
    const context = thrown ? `, closing the compiler after: ${messageOf(thrown.error).split("\n")[0] ?? ""}` :
      ", closing the compiler";
    throw new CompilerFailure("close", error, context);
  }
}
