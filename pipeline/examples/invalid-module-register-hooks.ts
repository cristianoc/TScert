// `registerHooks` installs a hook that runs inside every later module
// resolution of the process, writing the program's state then (run under
// Node: a resolution after `counting()` returns raises `count`). No entry of
// the overlay reviews it; the front end calls it through the host boundary
// tools/module-hooks.mts: refused where it is imported.
import { registerHooks } from "node:module";

export function counting(): { count: number } {
  const seen = { count: 0 };
  registerHooks({
    resolve: (specifier, context, next) => {
      seen.count = seen.count + 1;
      return next(specifier, context);
    },
  });
  return seen;
}
