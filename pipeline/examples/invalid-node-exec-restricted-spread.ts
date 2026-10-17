import { execFileSync } from "node:child_process";

// Options spreading an object whose type names no `env` may carry one, at
// any type: the host converts its values, running an object value's
// `toString`, which may shrink the array `map` visits, and the catching
// callback's result then has a hole. The copy meets neither form: the
// restricted one requires `env` absent, the other states it at strings.
export function wrong(
  scripts: string[],
  extra: { encoding: "utf8" },
): string[] {
  const stdio: readonly ["pipe", "pipe", "ignore"] = ["pipe", "pipe", "ignore"];
  return scripts.map((s: string): string => {
    try {
      return execFileSync("node", ["-e", s], { ...extra, stdio });
    } catch {
      return "";
    }
  });
}
