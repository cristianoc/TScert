// Census functions:
// compiler-channel.mts#privateClient
// compiler-channel.mts#compilerLedger
// compiler-channel.mts#abandonCompiler
// compiler-channel.mts#abandon
import { API } from "typescript/unstable/sync";

import { fieldOf } from "../../tools/thrown.mts";

import {
  clientHasMethod,
  requestMembers,
} from "../../tools/client-prototype.mts";

interface CompilerProcess {
  readonly pid?: number;
  readonly exitCode: number | null;
  readonly signalCode: string | null;
  kill(signal: "SIGKILL"): boolean;
  once(event: "exit", listener: () => void): unknown;
}

interface PrivateClient {
  close(): void;
  readonly channel: { readonly child: CompilerProcess };
}

const isProcedure = (f: unknown): f is () => unknown => typeof f === "function";

export function privateClient(api: API): PrivateClient {
  const client = fieldOf(api, "client");
  const missing = (member: string): Error =>
    Error(
      `the compiler package's private shape changed: API.client${member} is missing (compiler-channel.mts)`,
    );
  if (!client || typeof client !== "object") throw missing("");
  if (!("close" in client) || !isProcedure(client.close))
    throw missing(".close");
  for (const member of requestMembers)
    if (!clientHasMethod(api, member)) throw missing(`.${member}`);
  const child = fieldOf(fieldOf(client, "channel"), "child");
  if (
    !child ||
    typeof child !== "object" ||
    !("kill" in child) ||
    !isProcedure(child.kill) ||
    !("once" in child) ||
    !isProcedure(child.once) ||
    !("exitCode" in child) ||
    !("signalCode" in child)
  )
    throw missing(".channel.child");
  return client as PrivateClient; // asserted: the decoder of the private client, each member it names checked above
}
