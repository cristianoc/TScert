// A module constant whose initializer establishes its argument's presence,
// read by a later closure: `dir` is a string wherever it is read. The
// equivalent of a top-level `if (dir === undefined) throw …` after the
// declaration, a statement outside the fragment. Stands for the census
// functions unchecked.mts#decodeResult and #findIn, whose slices read
// `projectDir` in `runPart`.
function present(argument: string | undefined): string {
  if (argument === undefined) throw new Error("usage: --project DIR");
  return argument;
}

const args = ["--project", "tools"];
const at = args.indexOf("--project");
const dir = at < 0 ? "tools" : present(args[at + 1]);
export const run = (part: number): string[] => [dir, `${part}`];
