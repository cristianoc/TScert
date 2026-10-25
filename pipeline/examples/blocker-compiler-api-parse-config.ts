// Census functions: declaration-session.mts#collect, #inDeclarationSession.
// The API view includes parseConfigFile; reading API's conditional
// updateSnapshot parameter requires instantiation of the class's parameter.
import type { API } from "typescript/unstable/sync";
export function use(api: API, file: string): number {
  return api.parseConfigFile(file).fileNames.length;
}
