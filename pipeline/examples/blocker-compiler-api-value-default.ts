// A value import of the compiler API's class `API`, used as a type: the
// class is read through its named view, which lists no constructor, so the
// default of its type parameter is not read.
// Census functions:
// compiler-channel.mts#abandon, compiler-channel.mts#abandonCompiler,
// compiler-channel.mts#compilerLedger, compiler-channel.mts#openCompiler,
// compiler-channel.mts#openFrontEndCompiler,
// compiler-channel.mts#privateClient, compiler-channel.mts#releaseCompiler.
import { API } from "typescript/unstable/sync";
export function use(api: API): void {
  api.close();
}
