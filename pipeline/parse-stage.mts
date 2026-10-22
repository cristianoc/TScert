// The observed stages of the entry point (DESIGN.md, "Observed stages"): the
// parse and TypeScript's diagnostics, each run in this process with fresh
// compilers, their values stored as text and decoded field by field.
// ../tools/fragment-parse.mts is the trusted parser and syntactic gate: without it no source becomes the Fragment the producer and Lean read.
import { close as closeParser, parseFile } from "../tools/fragment-parse.mts";
import { clientErrors, type SeenDiagnostic } from "../tools/declaration-graph.mts";
import { messageOf, passToolFailure } from "../tools/thrown.mts";
import { activeFamilies } from "../tools/family-activation.mts";
import { compilerImplementation } from "../tools/compiler-channel.mts";
import type { InProcessCall } from "./in-process-execution.mts";

/** The parse stage of the snapshot `file` of the source `bytes`, read in the
 * project `tsconfigPath` (or its own) with imports resolved as `resolution`'s,
 * under the active family descriptions: an observed stage. */
export function parseCall(bytes: Buffer, file: string, tsconfigPath: string | undefined, resolution: string):
    InProcessCall<Parsed> {
  return {
    stage: "parse",
    inputs: [{ role: "source", bytes }, { role: "file", bytes: file }, { role: "resolution", bytes: resolution },
      { role: "project", bytes: tsconfigPath ?? "" }, { role: "families", bytes: JSON.stringify(activeFamilies()) }],
    run: () => parseStage(file, tsconfigPath, resolution),
    codec: parsedCodec,
    observed: { compiler: compilerImplementation },
  };
}

/** The TypeScript diagnostics stage: the errors TypeScript reports for
 * `file` in its project, an observed stage. */
export function diagnosticsCall(file: string, tsconfigPath: string | undefined): InProcessCall<SeenDiagnostic[]> {
  return {
    stage: "diagnostics",
    inputs: [{ role: "file", bytes: file }, { role: "project", bytes: tsconfigPath ?? "" }],
    run: () => diagnosticsStage(file, tsconfigPath),
    codec: diagnosticsCodec,
    observed: { compiler: compilerImplementation },
  };
}

/** A parse's value: its Fragment as text, or its refusal, and the TypeScript
 * errors its gate read. */
export type Parsed = { code: number; out: string; detail: string; seen: SeenDiagnostic[] };

/** The parser run on `file`, read in the project `tsconfigPath` (or its own)
 * with imports resolved as `resolution`'s, by a compiler opened for it and
 * released after it. */
function parseStage(file: string, tsconfigPath: string | undefined, resolution: string): Parsed {
  const seen: SeenDiagnostic[] = [];
  closeParser();
  try {
    return { code: 0, out: JSON.stringify(parseFile(file, false, tsconfigPath, resolution, (d) => seen.push(d))),
      detail: "", seen };
  } catch (error) {
    // A tool failure is no result: the stage fails, and nothing is stored.
    passToolFailure(error);
    if (messageOf(error).startsWith("tool failure:")) throw error;
    return { code: 1, out: "", detail: messageOf(error), seen };
  } finally {
    closeParser();
  }
}

/** The errors TypeScript reports for `file` in its project; none where its
 * project does not load. */
function diagnosticsStage(file: string, tsconfigPath: string | undefined): SeenDiagnostic[] {
  try {
    return clientErrors(file, tsconfigPath);
  } catch (error) {
    passToolFailure(error);
    return [];
  }
}

/** A JSON value's field. */
const field = (value: unknown, key: string): unknown =>
  typeof value === "object" && value !== null && Object.hasOwn(value, key) ? Object.getOwnPropertyDescriptor(value, key)?.value
    : undefined;
const exactly = (value: unknown, keys: readonly string[]): boolean =>
  typeof value === "object" && value !== null && !Array.isArray(value) &&
  Object.keys(value).sort().join() === [...keys].sort().join();
const position = (value: unknown): { line: number; character: number } | null => {
  const line = field(value, "line"), character = field(value, "character");
  return exactly(value, ["line", "character"]) && typeof line === "number" && typeof character === "number"
    ? { line, character } : null;
};
/** A stored diagnostic, field by field. */
function readSeen(value: unknown): SeenDiagnostic {
  const file = field(value, "file"), client = field(value, "client"), pos = field(value, "pos"), text = field(value, "text");
  const start = position(field(value, "start")), end = position(field(value, "end"));
  if (!exactly(value, ["file", "client", "pos", "start", "end", "text"]) || typeof file !== "string" ||
      typeof client !== "boolean" || !Array.isArray(pos) || pos.length !== 2 || typeof pos[0] !== "number" ||
      typeof pos[1] !== "number" || !start || !end || typeof text !== "string")
    throw Error("a stored diagnostic is malformed");
  return { file, client, pos: [pos[0], pos[1]], start, end, text };
}
const readSeenList = (value: unknown): SeenDiagnostic[] => {
  if (!Array.isArray(value)) throw Error("stored diagnostics are no list");
  return value.map(readSeen);
};

/** The parse's value as stored, and back. */
export const parsedCodec: { encode: (value: Parsed) => Buffer; decode: (bytes: Buffer) => Parsed } = {
  encode: (value: Parsed): Buffer => Buffer.from(JSON.stringify(value), "utf8"),
  decode: (bytes: Buffer): Parsed => {
    const value: unknown = JSON.parse(bytes.toString("utf8"));
    const code = field(value, "code"), out = field(value, "out"), detail = field(value, "detail");
    if (!exactly(value, ["code", "out", "detail", "seen"]) || typeof code !== "number" || typeof out !== "string" ||
        typeof detail !== "string")
      throw Error("a stored parse is malformed");
    return { code, out, detail, seen: readSeenList(field(value, "seen")) };
  },
};
/** The diagnostics' value as stored, and back. */
export const diagnosticsCodec: { encode: (value: SeenDiagnostic[]) => Buffer; decode: (bytes: Buffer) => SeenDiagnostic[] } = {
  encode: (value: SeenDiagnostic[]): Buffer => Buffer.from(JSON.stringify(value), "utf8"),
  decode: (bytes: Buffer): SeenDiagnostic[] => readSeenList(JSON.parse(bytes.toString("utf8"))),
};
