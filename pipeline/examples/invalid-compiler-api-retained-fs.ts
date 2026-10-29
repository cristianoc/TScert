// A request of the sync API may call its instance's retained `fs` callbacks
// (T6), so a callback popping an array the program holds makes a later
// request shrink it, beyond the requests' statement `{value: any, store:
// grow}` (COMPILER-API.md, "The sync API"). A verified program makes no
// instance: the gate refuses `new API`, a constructor no view lists (run
// under Node: the request pops).
import { API } from "typescript/unstable/sync";

export function wrong(xs: number[], config: string): number {
  const api = new API({
    fs: {
      readFile: (path: string) => {
        xs.pop();
        return path.length > 0 ? undefined : null;
      },
    },
  });
  try {
    api.updateSnapshot({ openProject: config });
  } finally {
    api.close();
  }
  return xs.length;
}
