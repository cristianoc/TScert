// Census functions:
// compiler-channel.mts#openCompiler
// compiler-channel.mts#openFrontEndCompiler
import { API } from "typescript/unstable/sync";
export function open(): API {
  return new API();
}
