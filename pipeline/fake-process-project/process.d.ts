// A `process` a declaration file of the project declares, its member spelled
// exactly as Node's `@types/node` spells it: the origin is the project, not
// the package the reviewed entry names.
interface FakeProcess {
  argv: string[];
}
declare var process: FakeProcess;
