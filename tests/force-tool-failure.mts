// A forced failure of the compiler's API, for `tool-failures.mts`: imported
// (in process, or by `--import` in `NODE_OPTIONS` for a child), it wraps the
// synchronous channel's request so that a request whose JavaScript stack
// holds a frame matching `TSCERT_FORCE_FRAME`, or whose payload names
// `TSCERT_FORCE_PAYLOAD`, throws before it is sent: a stack exhaustion
// (`TSCERT_FORCE_KIND=stack`, the default) or a panic the compiler replied
// (`panic`). With `TSCERT_FORCE_AFTER_SEND`, a stack exhaustion is thrown
// after the request is written and before its reply is read, which leaves
// the reply unread on the channel. `TSCERT_FORCE_LIMIT` bounds how many
// requests of this process fail. Each forced failure appends a line to
// `TSCERT_FORCE_FIRED`, and so does each later request on a channel a stack
// exhaustion was forced on (`later <method>`), whose replies may be unread.
import { appendFileSync, realpathSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";

// The module as Node loads it for the front end, at its real path.
const channelModule = pathToFileURL(realpathSync(fileURLToPath(
  new URL("../tools/node_modules/typescript/dist/api/syncChannel.js", import.meta.url)))).href;
const loaded: unknown = await import(channelModule);
/** An own property of an object or a function, `undefined` elsewhere. */
const own = (value: unknown, key: string): unknown =>
  (typeof value === "object" && value !== null) || typeof value === "function"
    ? Object.getOwnPropertyDescriptor(value, key)?.value : undefined;
const prototype: unknown = own(own(loaded, "SyncRpcChannel"), "prototype");
const original: unknown = own(prototype, "requestBytesSync");
/** The channel's request, as the wrapper calls it: a method of the channel
 * taking the method's name and its payload. */
const isRequest = (f: unknown): f is (this: unknown, method: unknown, payload: unknown) => unknown =>
  typeof f === "function";
/** The channel's write of a message, `[type, name, payload]`, and the bytes
 * of a method's name. */
const isWrite = (f: unknown): f is (this: unknown, type: number, name: unknown, payload: unknown) => unknown =>
  typeof f === "function";
const isNameBytes = (f: unknown): f is (this: unknown, method: unknown) => unknown => typeof f === "function";
const write: unknown = own(prototype, "writeTuple");
const nameBytes: unknown = own(prototype, "getMethodBuf");
if (!prototype || typeof prototype !== "object" || !isRequest(original) || !isWrite(write) || !isNameBytes(nameBytes))
  throw Error("the compiler's synchronous channel has no requestBytesSync, writeTuple or getMethodBuf to wrap");
/** The channel's code for a request message. */
const REQUEST = 1;

/** Whether a request is forced to fail, read from the environment at each
 * request, so that a test can change it between parses. */
let failures: number = 0;
const damaged = new WeakSet<object>();
const forced = (method: unknown, payload: unknown): boolean => {
  const limit = process.env["TSCERT_FORCE_LIMIT"];
  if (limit && failures >= Number(limit)) return false;
  const frame = process.env["TSCERT_FORCE_FRAME"];
  const named = process.env["TSCERT_FORCE_PAYLOAD"];
  if (frame && new RegExp(frame).test(new Error().stack ?? "")) return true;
  if (!named) return false;
  const text = typeof payload === "string" ? payload : payload instanceof Uint8Array ? Buffer.from(payload).toString("utf8") : "";
  return method === "updateSnapshot" && text.includes(named);
};

Error.stackTraceLimit = 200;
Object.assign(prototype, {
  requestBytesSync: function (this: unknown, method: unknown, payload: unknown): unknown {
    const fired = process.env["TSCERT_FORCE_FIRED"];
    const channel = typeof this === "object" && this !== null ? this : null;
    if (channel && damaged.has(channel) && fired) appendFileSync(fired, `later ${String(method)}\n`);
    if (forced(method, payload)) {
      failures++;
      if (fired) appendFileSync(fired, `${String(method)}\n`);
      const panic = process.env["TSCERT_FORCE_KIND"] === "panic";
      if (channel && !panic) damaged.add(channel);
      if (process.env["TSCERT_FORCE_AFTER_SEND"]) {
        write.call(this, REQUEST, nameBytes.call(this, method), payload);
        throw new RangeError("Maximum call stack size exceeded");
      }
      throw panic ? new Error("panic: forced by tests/force-tool-failure.mts")
        : new RangeError("Maximum call stack size exceeded");
    }
    return original.call(this, method, payload);
  },
});
