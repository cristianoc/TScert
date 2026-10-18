// A returned function taking the branded string, returned again: the client
// would call it with a plain string (reading rule 5).
import { curried } from "@fixture/host";

export function run(): void {
  curried()()("plain");
}
