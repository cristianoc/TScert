// A value import used only as a type eagerly reads the imported class type-
// parameter default.
// Census functions:
// compiler-channel.mts#abandon, compiler-channel.mts#abandonCompiler,
// compiler-channel.mts#compilerLedger, compiler-channel.mts#openCompiler,
// compiler-channel.mts#openFrontEndCompiler,
// compiler-channel.mts#privateClient, compiler-channel.mts#releaseCompiler.
import { API } from "typescript/unstable/sync";
export function use(api: API): void {}
