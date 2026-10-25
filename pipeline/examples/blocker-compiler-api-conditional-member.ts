// An API instance at the type argument false needs its conditional member type
// evaluated at that argument.
// Census functions:
// declaration-graph.mts#clientErrors, declaration-graph.mts#withOwnProject,
// declaration-graph.mts#withProject, declaration-session.mts#asideForTests,
// declaration-session.mts#close, declaration-session.mts#discard,
// declaration-session.mts#inDeclarationAttempt,
// declaration-session.mts#incompatibility,
// declaration-session.mts#noteAutomaticCollection,
// declaration-session.mts#releaseDeclarationSession,
// declaration-session.mts#retainDeclarationSessions,
// declaration-session.mts#settleDeclarationSession, fragment-parse.mts#close,
// fragment-parse.mts#openFile, fragment-parse.mts#openText,
// fragment-parse.mts#projectFor, fragment-parse.mts#release.
import type { API } from "typescript/unstable/sync";
export function use(api: API): void {
  api.close();
}
