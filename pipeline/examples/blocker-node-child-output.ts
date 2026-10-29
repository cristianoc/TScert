// A worker run through the host boundary tools/child-output.mts, as
// unchecked.mts runs its parts: the program receives the child's exit code,
// signal and standard output as plain values, and holds no child, stream or
// listener.
// Census functions: unchecked.mts#check, unchecked.mts#findIn.
import { runChild } from "../../tools/child-output.mts";

export async function output(
  command: string,
  args: readonly string[],
): Promise<string> {
  const ran = await runChild(command, args);
  if (ran.code !== 0)
    throw new Error(
      `${command} failed (${ran.code ?? ran.signal ?? "no exit code"})`,
    );
  return ran.stdout;
}
