/* Part of the trusted front end: running a child process and collecting its
 * standard output, the one use the front end makes of `spawn` (unchecked.mts
 * runs its workers). Node publishes the child on a diagnostics channel
 * before `spawn` returns, so other code may hold it: replace its `stdout` or
 * its methods, change the stream's encoding, remove listeners, or emit
 * `data`, `close` and `error` with any arguments. This module is a host
 * boundary that holds the child, its stream and its listeners and hands its
 * caller plain values only (SOURCE-REWRITES.md, "A child's output"). What it
 * promises is their types, not their provenance. */
import { spawn } from "node:child_process";

/** A child's exit code, the signal that ended it, and its standard output. */
export type ChildOutput = { code: number | null; signal: string | null; stdout: string };

/** Runs `command` with `args`, its standard input ignored, its standard
 * output collected and its standard error inherited. The promise, where it
 * settles, resolves to a `ChildOutput` or rejects; it settles once. Where no
 * other code holds the child, it resolves with the exit code, the signal and
 * the output decoded as UTF-8 once the child closes, and rejects where the
 * child cannot start (no such command, no file descriptors left). Where
 * other code holds it, the values may be ones that code emitted, the output
 * may be decoded otherwise, and the promise may stay pending; an `error`
 * emitted after that code removed this module's listener ends the process. */
export function runChild(command: string, args: readonly string[]): Promise<ChildOutput> {
  return new Promise<ChildOutput>((resolve, reject) => {
    let settled = false;
    // A fixed message: a payload is read nowhere, since reading it may run
    // code of whoever emitted it.
    const fail = (message: string): void => {
      if (settled) return;
      settled = true;
      reject(new Error(`${command}: ${message}`));
    };
    try {
      const child = spawn(command, args, { stdio: ["ignore", "pipe", "inherit"] });
      child.on("error", () => fail("the child failed to start or was signalled an error"));
      const stdout: unknown = child.stdout;
      if (stdout === null || typeof stdout !== "object" || !("setEncoding" in stdout) || !("on" in stdout)) {
        fail("no standard output stream");
        return;
      }
      const stream = child.stdout;
      if (stream === null || stream !== stdout) {
        fail("standard output changed");
        return;
      }
      stream.setEncoding("utf8");
      let out = "";
      stream.on("data", (...delivered: unknown[]) => {
        if (settled) return;
        const [chunk] = delivered;
        if (delivered.length === 1 && typeof chunk === "string") out += chunk;
        else fail("standard output delivered no text");
      });
      child.on("close", (...delivered: unknown[]) => {
        if (settled) return;
        const [code, signal] = delivered;
        if (delivered.length !== 2 || !(code === null || typeof code === "number") ||
            !(signal === null || typeof signal === "string")) {
          fail("closed with unexpected arguments");
          return;
        }
        settled = true;
        resolve({ code, signal, stdout: out });
      });
    } catch {
      // Whatever was thrown (by spawn, by a replaced method or getter) is
      // not read. The child is left to end on its own: its pid is a property other
      // code may have replaced, and a child that never started has none.
      fail("starting the child or reading its standard output threw");
    }
  });
}
