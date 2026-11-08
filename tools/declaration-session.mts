/* Part of the trusted front end: the declaration compiler of a named project,
 * retained between collections (STAGE-STORE.md, "Retained declaration
 * sessions"). A collection that names its project (`tsconfigOf`) reads it
 * in a session: a compiler at the resolution file's directory with exactly
 * that project open, no document open and no overlay. A worker that retains
 * sessions (`retainDeclarationSessions`) keeps one idle session, and a later
 * collection uses it where it is compatible: the same project, the same
 * directory, the same compiler and the same active host families; its
 * ledger, every answer the file system gave its compiler over its lifetime,
 * holding now; and the process's caches consistent. Otherwise the session is
 * released and a new one opened.
 *
 * A collection's probes replace project files by an overlay; the collection
 * ends by restoring the base project, the overlay cleared and the compiler
 * told of every path it replaced, and checking the restored state. A
 * restoration that fails, or a state that is not the base one, releases the
 * session and makes the current records incomplete, so the attempt using it
 * publishes nothing.
 *
 * The ledger is noted in every record a reused session's collection makes,
 * and accumulates its new answers. `settleDeclarationSession` checks it
 * again at an attempt's end, before its publication. */
import { createHash } from "node:crypto";
import { dirname, join, resolve } from "node:path";
import type { API, Project, Snapshot } from "typescript/unstable/sync";
/** What a snapshot request asks: the parameter of `API.updateSnapshot`. */
import type { UpdateSnapshotParams } from "typescript/unstable/proto";
import { abandonCompiler, compilerChoice, openDocuments, openFrontEndCompiler, releaseCompiler } from "./compiler-channel.mts";
import { activeFamilies } from "./family-activation.mts";
import { importLedger, ledgerAnswers, ledgerState, newLedger, processInconsistency, processRetirement, unobservable, validateLedger,
  withLedger, type Ledger, type Noted } from "./files.mts";
import { fieldOf, messageOf, toolFailureOf } from "./thrown.mts";
import type { ProbeProgram } from "./type-probe.mts";

/** A session: its compiler, the overlay its probes write, what it is
 * compatible with, its ledger and its snapshots. */
type Session = {
  api: API;
  overlay: Map<string, string>;
  /** The compiler's working directory, the resolution file's directory. */
  cwd: string;
  /** The named project, normalized. */
  config: string;
  /** The compatibility descriptor: project, directory, compiler and families. */
  descriptor: string;
  generation: number;
  uses: number;
  ledger: Ledger;
  /** The latest snapshot, the idle session's base. */
  idle: Snapshot | null;
};

/** A session's request for a snapshot: it names no file to open, so a
 * session holds no open document. */
function update(s: Session, params: UpdateSnapshotParams): Snapshot {
  if (params.openFiles?.length) throw Error("a declaration session opens no document");
  return s.api.updateSnapshot(params);
}

/** What the sessions did in this process, for the controls. */
export type SessionTelemetry = {
  /** Compilers opened for named projects. */
  opens: number;
  /** Collections that used a retained session. */
  reuses: number;
  /** Retained sessions released for an incompatible collection or an
   * invalid ledger, and why the last one was. */
  replacements: number;
  lastReplacement: string | null;
  /** Sessions released after a failure or an unclean state, and why the
   * last one was. */
  discarded: number;
  lastDiscard: string | null;
  /** Collections of an automatically selected project. */
  automatic: number;
  /** Probe programs made in sessions. */
  probes: number;
};
let telemetry: SessionTelemetry = { opens: 0, reuses: 0, replacements: 0, lastReplacement: null, discarded: 0,
  lastDiscard: null, automatic: 0, probes: 0 };
export const declarationSessionTelemetry = (): SessionTelemetry => ({ ...telemetry });

/** The idle session and what it holds, for the controls: its generation,
 * uses, directory, project, open projects and documents, overlay and ledger size; null
 * where none is retained. */
export type RetainedSession = { generation: number; uses: number; cwd: string; config: string; projects: string[];
  documents: number; overlay: number; ledger: number };
export function retainedDeclarationSession(): RetainedSession | null {
  const s = retained;
  if (!s) return null;
  return { generation: s.generation, uses: s.uses, cwd: s.cwd, config: s.config,
    projects: s.idle ? s.idle.getProjects().map((p) => p.configFileName) : [], documents: openDocuments(s.api).length,
    overlay: s.overlay.size, ledger: ledgerState(s.ledger).answers };
}

/** Tests only: `run` in fresh compilers, the retained session, retention
 * and the telemetry set aside and restored after it. */
export function asideForTests<T>(run: () => T): T {
  const held = retained, was = retaining, counts = { ...telemetry };
  retained = null;
  retaining = false;
  try {
    return run();
  } finally {
    retained = held;
    retaining = was;
    telemetry = counts;
  }
}
/** Tests only: the retained session's ledger. */
export const retainedLedgerForTests = (): Noted[] => retained ? ledgerAnswers(retained.ledger) : [];

let retaining: boolean = false;
let retained: Session | null = null;
let generations: number = 0;
/** For each observed attempt running (`inDeclarationAttempt`), innermost
 * last, the ledgers of the sessions its collections used, released ones
 * included; a nested attempt's collections are its enclosing attempts' too. */
const attempts: Ledger[][] = [];

/** Retain a session between collections from now on, or not: a worker
 * serving checks retains one; turning retention off releases it. */
export function retainDeclarationSessions(on: boolean): void {
  retaining = on;
  if (!on) releaseDeclarationSession();
}

/** A collection of an automatically selected project, in a compiler of its
 * own: the retained session is released. */
export function noteAutomaticCollection(): void {
  telemetry.automatic++;
  const s = retained;
  retained = null;
  if (s) {
    telemetry.replacements++;
    telemetry.lastReplacement = "an automatically selected project";
    close(s);
  }
}

/** Release the retained session: at a worker's end, its retirement or the
 * end of a command. */
export function releaseDeclarationSession(): void {
  const s = retained;
  retained = null;
  if (s) close(s);
}

/** Tests only: a fault the next collection makes, to show it is caught: its
 * restoration fails, it leaves an overlay entry, it leaves the project
 * `project` open besides its own, it asks to open the document `document`
 * through the session's requests, or opens it bypassing them, or it runs
 * `during` within the session's ledger (reads of its own, an incomplete one,
 * a compiler's read of a configuration by request). */
export type SessionFault = { kind: "restoration" } | { kind: "overlay" } | { kind: "project"; project: string } |
  { kind: "document-request"; document: string } | { kind: "document-left"; document: string } |
  { kind: "during"; during: (compilerRead: (config: string) => void) => void };
let fault: SessionFault | null = null;
export function injectSessionFaultForTests(injected: SessionFault | null): void {
  fault = injected;
}

/** Close a session's compiler: its snapshots by request, then its process;
 * a failure closing it abandons it. */
function close(s: Session): void {
  try {
    releaseCompiler(s.api, null);
  } catch {
    // releaseCompiler abandoned it; the session is gone either way.
  }
}
/** Release a session whose state is uncertain, without a request. */
function discard(s: Session, reason: string): void {
  telemetry.discarded++;
  telemetry.lastDiscard = reason;
  abandonCompiler(s.api);
}

/** Why the retained session cannot serve a collection described by
 * `descriptor`, or null. */
function incompatibility(s: Session, descriptor: string): string | null {
  if (s.descriptor !== descriptor) return "another project, directory, compiler or family configuration";
  if (s.overlay.size !== 0 || openDocuments(s.api).length !== 0) return "the session's base state is not clean";
  return validateLedger(s.ledger);
}

/** The project of a module's lowering: the named project's options, its
 * root files the module and the declaration files among the named
 * project's roots, which state what every file of it sees, a file of its own
 * name beside the named project's (`fixed`, which no probe replaces). Its
 * compiler reads the module, what it imports and those declarations, and no
 * other file of the named project, so an edit of an importer leaves the
 * module's observations unchanged (STAGE-STORE.md, "Shared work"). */
export const moduleProject = (named: string, root: string): string =>
  join(dirname(named), `tsconfig.module-${createHash("sha256").update(root).digest("hex").slice(0, 16)}.json`);
export function moduleProjectText(api: API, named: string, root: string): string {
  const names = fieldOf(api.parseConfigFile(named), "fileNames");
  const declarations = Array.isArray(names)
    ? names.filter((n): n is string => typeof n === "string" && n.endsWith(".d.ts")).map((n) => resolve(dirname(named), n))
    : [];
  return JSON.stringify({ extends: named, files: [root, ...declarations], include: [root, ...declarations] });
}

/** `use` over the project `tsconfigPath` names, as it loads with `file`
 * resolved from its directory, or, given a module `root`, over that
 * project rooted at the module (`moduleProject`): in the retained session
 * where it is compatible, else in a new one, retained afterwards where
 * retention is on and its state is clean. `use` receives the project (or
 * undefined where the compiler did not load it) and the probe of its files. */
export function inDeclarationSession<T>(file: string, tsconfigPath: string,
    use: (project: Project | undefined, probe: ProbeProgram) => T, root?: string): T {
  const named = resolve(tsconfigPath);
  const cwd = dirname(file);
  if (root !== undefined) {
    // A module's lowering opens a session of its own, released after it,
    // and leaves the retained session as it is: its compiler gets no
    // request, so its ledger reaches no record of the module's stage.
    const config = moduleProject(named, resolve(root));
    const overlay = new Map<string, string>(), fixed = new Map<string, string>();
    const ledger = newLedger();
    const api = openFrontEndCompiler(cwd, overlay, ledger, fixed);
    fixed.set(config, withLedger(ledger, () => moduleProjectText(api, named, resolve(root))));
    const descriptor = JSON.stringify({ role: "module", config, cwd, compiler: compilerChoice(), families: activeFamilies() });
    const own: Session = { api, overlay, cwd, config, descriptor, generation: ++generations, uses: 1, ledger, idle: null };
    for (const used of attempts) if (!used.includes(ledger)) used.push(ledger);
    const was = retaining;
    retaining = false;
    try {
      return collect(own, use);
    } finally {
      retaining = was;
    }
  }
  const config = named;
  const descriptor = JSON.stringify({ role: "declaration", config, cwd, compiler: compilerChoice(),
    families: activeFamilies() });
  let session: Session | null = null;
  const held = retained;
  retained = null;
  if (held) {
    const reason = incompatibility(held, descriptor);
    if (reason === null) {
      session = held;
      session.uses++;
      telemetry.reuses++;
      importLedger(session.ledger);
    } else {
      telemetry.replacements++;
      telemetry.lastReplacement = reason;
      close(held);
    }
  }
  if (!session) {
    const overlay = new Map<string, string>();
    // The session's ledger is its compiler's (`compilerLedger`).
    const ledger = newLedger();
    session = { api: openFrontEndCompiler(cwd, overlay, ledger), overlay, cwd, config, descriptor,
      generation: ++generations, uses: 1, ledger, idle: null };
    telemetry.opens++;
  }
  for (const used of attempts) if (!used.includes(session.ledger)) used.push(session.ledger);
  return collect(session, use);
}

function collect<T>(s: Session, use: (project: Project | undefined, probe: ProbeProgram) => T): T {
  // The paths the probes replaced, read from disk again by the next probe
  // and by the restoration; a probe's snapshot is released when the next is
  // made, which takes its unchanged files over from it.
  let replaced: string[] = [];
  const snapshots: { base: Snapshot | null; probed: Snapshot | null } = { base: null, probed: null };
  const probe: ProbeProgram = (files, read) => {
    s.overlay.clear();
    for (const [name, text] of files) s.overlay.set(name, text);
    telemetry.probes++;
    const snapshot = update(s, { fileChanges: { changed: [...new Set([...replaced, ...files.keys()])] } });
    replaced = [...files.keys()];
    snapshots.probed?.dispose();
    snapshots.probed = snapshot;
    const project = snapshot.getProject(s.config);
    if (!project) throw Error("TypeScript did not load the probe program");
    return read(project.program, project.checker);
  };
  let thrown: { error: unknown } | null = null;
  let result: { value: T } | null = null;
  try {
    result = { value: withLedger(s.ledger, () => {
      // The project is opened once, by the session's first snapshot; a
      // later collection reacquires it in a snapshot of its own.
      const base = update(s, s.idle === null ? { openProjects: [s.config] } : {});
      snapshots.base = base;
      s.idle?.dispose();
      s.idle = null;
      const injected = fault;
      if (injected?.kind === "during") {
        const { during } = injected;
        fault = null;
        during((config) => void s.api.parseConfigFile(config));
      }
      return use(base.getProject(s.config), probe);
    }) };
  } catch (error) {
    thrown = { error };
  }
  const failure = thrown && toolFailureOf(thrown.error);
  if (thrown && failure) {
    // A tool failure leaves the compiler's state unknown: released as
    // `releaseCompiler` does after it, never retained.
    telemetry.discarded++;
    telemetry.lastDiscard = messageOf(thrown.error).split("\n")[0] ?? "";
    releaseCompiler(s.api, thrown);
    throw thrown.error;
  }
  if (!retaining) {
    releaseCompiler(s.api, thrown);
  } else {
    const unclean = restore(s, replaced, [snapshots.probed, snapshots.base]);
    const state = ledgerState(s.ledger);
    const reason = unclean ?? state.incomplete ?? state.inconsistent ?? processInconsistency() ?? processRetirement();
    if (unclean !== null) {
      // An uncertain restoration: whatever used this session publishes nothing.
      unobservable(`the declaration session's restoration failed: ${unclean}`);
      discard(s, unclean);
    } else if (reason !== null) {
      telemetry.discarded++;
      telemetry.lastDiscard = reason;
      close(s);
    } else retained = s;
  }
  if (thrown) throw thrown.error;
  if (result === null) throw Error("a declaration collection neither returned nor threw");
  return result.value;
}

/** Restore a session's base state after a collection: the overlay cleared,
 * the compiler told of every path a probe replaced, the named project reacquired in a snapshot of its own, the
 * collection's snapshots (`obsolete`) released, and the state checked:
 * exactly that project open, no overlay and no open document (as the
 * compiler's requests count them, `openDocuments`). Why it is not restored,
 * or null. */
function restore(s: Session, replaced: readonly string[], obsolete: readonly (Snapshot | null)[]): string | null {
  try {
    return withLedger(s.ledger, () => {
      s.overlay.clear();
      // Only the injection and these branches write the fault: one read
      // decides which this restoration makes.
      const injected = fault;
      if (injected?.kind === "restoration") {
        fault = null;
        throw Error("an injected restoration failure");
      }
      const snapshot = update(s, replaced.length ? { fileChanges: { changed: [...replaced] } } : {});
      for (const old of obsolete) old?.dispose();
      s.idle = snapshot;
      if (injected?.kind === "overlay") {
        fault = null;
        s.overlay.set(resolve(s.cwd, "leaked.ts"), "");
      } else if (injected?.kind === "project") {
        const extra = injected.project;
        fault = null;
        s.idle = update(s, { openProjects: [extra] });
        snapshot.dispose();
      } else if (injected?.kind === "document-request") {
        const document = injected.document;
        fault = null;
        update(s, { openFiles: [document] });
      } else if (injected?.kind === "document-left") {
        const document = injected.document;
        fault = null;
        s.idle = s.api.updateSnapshot({ openFiles: [document] });
        snapshot.dispose();
      }
      const projects = s.idle.getProjects().map((p) => p.configFileName);
      if (projects.length !== 1 || projects[0] !== s.config)
        return `the session holds the projects ${JSON.stringify(projects)}, not only ${s.config}`;
      if (!s.idle.getProject(s.config)) return `the session does not hold ${s.config}`;
      if (s.overlay.size !== 0) return "the session's overlay is not empty";
      const open = openDocuments(s.api);
      if (open.length !== 0) return `the session holds the open documents ${JSON.stringify(open)}`;
      return null;
    });
  } catch (error) {
    return messageOf(error).split("\n")[0] ?? "the restoration failed";
  }
}

/** `run`, an observed attempt's computation, then, before its publication,
 * the ledger of every session its collections used, released ones included,
 * checked again (`settleDeclarationSession`). */
export function inDeclarationAttempt<T>(run: () => T): T {
  const used: Ledger[] = [];
  attempts.push(used);
  try {
    return run();
  } finally {
    attempts.splice(attempts.lastIndexOf(used), 1);
    settleDeclarationSession(used);
  }
}

/** The ledgers `ledgers` checked again: one that does not hold makes the
 * records being made incomplete, and releases its session where it is
 * retained. */
export function settleDeclarationSession(ledgers: readonly Ledger[]): void {
  for (const ledger of ledgers) {
    const reason = validateLedger(ledger);
    if (reason === null) continue;
    unobservable(`a declaration session's ledger does not hold at the attempt's end: ${reason}`);
    const s = retained;
    if (s !== null && s.ledger === ledger) {
      retained = null;
      telemetry.discarded++;
      telemetry.lastDiscard = reason;
      close(s);
    }
  }
}
