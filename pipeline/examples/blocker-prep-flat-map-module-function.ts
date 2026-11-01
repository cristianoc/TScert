// Census functions:
// compiler-channel.mts#profile
// compiler-channel.mts#identify
// compiler-channel.mts#current
// compiler-channel.mts#useInstallationForTests
// compiler-channel.mts#launcher
const named = (path: string): string[] => [
  ...new Set([path, path.replace(/^x/, "y")]),
];
export function paths(launcher: string, directory: string): string {
  return [launcher, directory]
    .flatMap(named)
    .map((p) => `(literal ${p})`)
    .join(" ");
}
