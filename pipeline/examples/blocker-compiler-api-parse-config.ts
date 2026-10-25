// Census functions: declaration-session.mts#collect, #inDeclarationSession.
// The API view includes parseConfigFile, and API is read at its default
// type argument false, where its conditional members are computed.
import type { API } from "typescript/unstable/sync";
export function use(api: API, file: string): number {
  return api.parseConfigFile(file).fileNames.length;
}
