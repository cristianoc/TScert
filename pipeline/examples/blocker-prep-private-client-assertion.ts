// Census functions:
// compiler-channel.mts#privateClient
// compiler-channel.mts#compilerLedger
// compiler-channel.mts#abandonCompiler
// compiler-channel.mts#abandon
import type { API } from "typescript/unstable/sync";
import {
  checkedPrivateClient,
  type PrivateClient,
} from "../../tools/client-prototype.mts";

export function privateClient(api: API): PrivateClient {
  return checkedPrivateClient(api);
}
