/* Part of the trusted front end: the front end's uses of Node's module
 * customization hooks (`registerHooks` of `node:module`), each from strings
 * to plain values, with the hooks it registers and the `require` it loads
 * through kept inside the function. A hook runs inside every module
 * resolution or load the process makes while it is registered, and other
 * code may register hooks around it (a subscriber of the `module.require`
 * tracing channel, the code of a module being loaded), which call it with
 * arguments of their own and hand it results of their own; such a hook may
 * keep the continuation that calls the boundary's and call it after the
 * boundary's function returned, when the hook only passes the call on to
 * the next step and records nothing. This module is a
 * host boundary that holds the hooks, checks every value they collect, and
 * hands its caller plain values only (SOURCE-REWRITES.md, "Module
 * customization hooks"). What it promises is their types, not their
 * provenance. Audited against Node 25.2.1's
 * `lib/internal/modules/customization_hooks.js`. */
import { createHash } from "node:crypto";
import { createRequire, registerHooks } from "node:module";
import { types } from "node:util";

/** The URL Node's own resolution resolves `specifier` to from the module
 * at the URL `parentHref`, under the conditions it enables in this process,
 * or `null` where it throws. Run through a resolve hook registered for the
 * call, which calls Node's resolution with that parent and resolves nothing
 * else; it loads nothing. Hooks other code registered earlier run inside
 * that resolution. */
export function resolveWithNode(specifier: string, parentHref: string): string | null {
  const probe = "tscert:resolve";
  const found: { url: string | null } = { url: null };
  const call = { active: true };
  const hooks = registerHooks({
    resolve: (requested, context, next) => {
      if (!call.active || requested !== probe) return next(requested, context);
      try {
        const url: unknown = next(specifier, { ...context, parentURL: parentHref }).url;
        found.url = typeof url === "string" ? url : null;
      } catch {
        // Whatever the resolution threw is not read.
        found.url = null;
      }
      return { url: "data:text/javascript,", shortCircuit: true };
    },
  });
  try {
    import.meta.resolve(probe);
  } finally {
    call.active = false;
    hooks.deregister();
  }
  return found.url;
}

/** The conditions Node's ES module resolution enables in this process
 * (`node`, `import`, `module-sync` and `node-addons` by default, and any
 * `--conditions`), read from a resolution's context through a resolve hook
 * registered for the call, a fresh array of strings. Throws where the hook
 * saw no resolution or the context held no array of strings. */
export function resolutionConditions(): string[] {
  const probe = "tscert:conditions";
  const seen: { conditions: unknown } = { conditions: null };
  const call = { active: true };
  const hooks = registerHooks({
    resolve: (specifier, context, next) => {
      if (!call.active || specifier !== probe) return next(specifier, context);
      seen.conditions = context.conditions;
      return { url: "data:text/javascript,", shortCircuit: true };
    },
  });
  try {
    import.meta.resolve(probe);
  } finally {
    call.active = false;
    hooks.deregister();
  }
  const read = seen.conditions;
  if (!Array.isArray(read)) throw Error("the resolve hook saw no resolution of the conditions probe");
  const conditions: string[] = [];
  for (const condition of read) {
    if (typeof condition !== "string") throw Error("a resolution's conditions hold a value that is no string");
    conditions.push(condition);
  }
  return conditions;
}

/** A module a load read: its URL, `null` where the load hook was called
 * with no string, and the SHA-256 of its source in hexadecimal digits, of a
 * string's UTF-8 encoding or a `Uint8Array`'s bytes as the load hook saw
 * them, `null` for a source of another kind. */
export type ModuleRead = { url: string | null; digest: string | null };
/** What loading a module came to: its value, or what the load threw. */
export type LoadOutcome = { k: "loaded"; value: unknown } | { k: "threw"; thrown: unknown };

/** The SHA-256 of a string's UTF-8 encoding or a `Uint8Array`'s bytes, in
 * hexadecimal digits; `null` for another value, or where hashing throws (a
 * detached buffer), its error unread. */
function digestOf(source: unknown): string | null {
  if (typeof source !== "string" && !types.isUint8Array(source)) return null;
  try {
    return createHash("sha256").update(source).digest("hex");
  } catch {
    return null;
  }
}

/** Node's loader for a module by its path: `require` of an ES module, which
 * shares the instance an `import` of the same file loads. */
const requireModule: (path: string) => unknown = createRequire(import.meta.url);

/** The module at the absolute `path`, as `require` loads it, and every
 * module read the load made, in the order its load hook saw them: run
 * through a load hook registered for the call and deregistered before it
 * returns. Loading runs the module's code and that of the modules it
 * loads, and hooks other code registered. The reads are a fresh array,
 * holding the calls made before the function returned. */
export function loadObserved(path: string): { reads: ModuleRead[]; outcome: LoadOutcome } {
  const reads: ModuleRead[] = [];
  const call = { active: true };
  const hooks = registerHooks({
    load: (url, context, next) => {
      if (!call.active) return next(url, context);
      const result = next(url, context);
      if (!call.active) return result;
      const source: unknown = result.source;
      reads.push({ url: typeof url === "string" ? url : null, digest: digestOf(source) });
      return result;
    },
  });
  let outcome: LoadOutcome;
  try {
    outcome = { k: "loaded", value: requireModule(path) };
  } catch (thrown) {
    outcome = { k: "threw", thrown };
  } finally {
    call.active = false;
    hooks.deregister();
  }
  return { reads: [...reads], outcome };
}
