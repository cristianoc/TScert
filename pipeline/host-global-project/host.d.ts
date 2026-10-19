// Globals a project declares for its host, outside any installed package:
// `hostNow`, which no reviewed entry lists, an overload of Node's
// `clearTimeout` whose text differs from the one reviewed, and a variable
// `hostConfig`, which no reviewed entry lists either.
declare function hostNow(): number;
declare function clearTimeout(timeout: number): void;
interface HostConfig {
  readonly level: number;
}
declare var hostConfig: HostConfig;
