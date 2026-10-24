// The execution adapter of in-process stages (DESIGN.md, "The stage store",
// keys). It describes an invocation (the stage, the node side's keyed code,
// the runtime, its inputs' digests and, for an observed stage, its compiler
// and the system's build), runs it, under observation for an observed stage,
// completes an observed stage's key with its observations, and stores and
// reads its value as text. The replay policy (`stages.mts`) chooses between
// running an invocation here and returning an entry whose stored description
// is its own.
import { observed, type Observation } from "../tools/files.mts";
import { canonical, codeFailure, inProcessCode, nodeIdentity, osBuild, sha256, type Canonical, type StageName }
  from "./stage-execution.mts";

/** A compiler's identity as an observed stage states it: its installation's
 * files and confinement, and whether it differs from disk now; or why its
 * reads are not all observed (`compilerImplementation` of
 * `tools/compiler-channel.mts`). */
export type CompilerIdentity =
  { identity: { [field: string]: string | boolean }; changed: () => boolean } | { unobserved: string };

/** A stage computed in this process: its known inputs by role, and its run
 * over exactly those inputs. A replayed stage's value is text, the result its
 * entry stores. Each stage's call is built by the stage's own module. */
export type InProcessCall<T> = {
  stage: StageName;
  inputs: readonly { role: string; bytes: string | Buffer }[];
  run: () => T;
  /** The value as stored, and back: for a stage that replays. */
  codec?: { encode: (value: T) => Buffer; decode: (bytes: Buffer) => T };
  /** An observed stage (STAGE-STORE.md, "Observed stages"): the compiler it
   * opens, and the file system's answers to its reads, are part of its key;
   * and its reads of its named inputs (`noteInput`), each evaluated again by
   * `inputs` before a replay. */
  observed?: { compiler: () => CompilerIdentity; inputs?: (name: string) => string | null };
};

/** An in-process invocation as bound: its description, before any
 * observation (an observed stage's pre-key), and why it is not
 * replay-eligible now, or null. */
export type BoundInProcess = {
  manifest: { readonly [key: string]: Canonical };
  input: string;
  identityFailure: () => string | null;
};

/** Bind an in-process call: its description names the stage, the node
 * side's keyed code (`inProcessCode`), the runtime, its inputs' digests and, for an observed stage, its compiler and the system's build. */
export function bindInProcess<T>(call: InProcessCall<T>): BoundInProcess {
  const runtime = nodeIdentity();
  const compiler = call.observed ? call.observed.compiler() : null;
  const manifest: { readonly [key: string]: Canonical } = {
    stage: call.stage,
    code: "identity" in inProcessCode ? inProcessCode.identity : null,
    runtime: "identity" in runtime ? runtime.identity : null,
    inputs: call.inputs.map((i) => [i.role, sha256(i.bytes)]),
    ...(compiler ? { compiler: "identity" in compiler ? compiler.identity : null, system: osBuild() } : {}),
  };
  const identityFailure = (): string | null => codeFailure(inProcessCode) ?? ("unidentified" in runtime ? runtime.unidentified
    : compiler && "unobserved" in compiler ? compiler.unobserved
    : compiler && compiler.changed() ? "the loaded compiler differs from disk"
    : compiler && osBuild() === null ? "the system's build is not identified"
    : null);
  return { manifest, input: canonical(manifest), identityFailure };
}

/** An in-process stage's run: its value, an observed stage's observations,
 * and why they are incomplete, or null. */
export type InProcessRun<T> = { value: T; observations: Observation[]; incomplete: string | null };

/** Run an in-process stage; an observed stage with its reads observed. Where
 * Node's caches disagree with the file system it fails. */
export function runInProcess<T>(call: InProcessCall<T>): InProcessRun<T> {
  if (!call.observed) return { value: call.run(), observations: [], incomplete: null };
  const made = observed(call.run);
  if (made.inconsistent !== null)
    throw Error(`the process's caches may disagree with the file system (${made.inconsistent}); a fresh process is needed`);
  // A named input's read the invocation does not answer as recorded is no
  // replayable observation: the entry is not published.
  const inputs = call.observed.inputs;
  const unanswered = made.observations.find(([o, name, answer]) =>
    o === "input" && (inputs === undefined || inputs(name) !== answer));
  return { value: made.value, observations: made.observations,
    incomplete: made.incomplete ?? (unanswered ? `the named input ${unanswered[1]} is not this invocation's` : null) };
}

/** An observed stage's description with its observations: the canonical
 * text its key is the digest of. */
export const observedInput = (manifest: { readonly [key: string]: Canonical }, observations: readonly Observation[]):
    string => canonical({ ...manifest, observations: observations.map(([operation, path, answer]) => [operation, path, answer]) });

/** A text value stored as its UTF-8 bytes. */
export const textCodec: { encode: (value: string) => Buffer; decode: (bytes: Buffer) => string } = {
  encode: (value: string): Buffer => Buffer.from(value, "utf8"),
  decode: (bytes: Buffer): string => bytes.toString("utf8"),
};
