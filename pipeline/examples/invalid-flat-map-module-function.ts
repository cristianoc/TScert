const box: { v: string | number } = { v: "ok" };

const named = (path: string): string[] => {
  box.v = 1;
  return [...new Set([path, path.replace(/^x/, "y")])];
};

export function paths(launcher: string, directory: string): string {
  if (typeof box.v !== "string") return "";
  [launcher, directory].flatMap(named);
  return box.v;
}
