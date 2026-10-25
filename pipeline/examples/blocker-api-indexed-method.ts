// The Parameters utility type needs the declared method signature recovered
// from an indexed class member.
// Census functions:
// declaration-session.mts#update.
import type { API } from "typescript/unstable/sync";
type Params = Parameters<API["updateSnapshot"]>;
export function use(x: Params): void {}
