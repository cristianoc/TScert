// The sync API's client serializes what an instance's retained `fs`
// callback returns with `JSON.stringify`, so a callback returning an object
// whose `toJSON` pops an array the program holds makes a request shrink
// it, beyond the requests' statement `{value: any, store: grow}`, though
// the callback itself changes nothing (COMPILER-API.md, "The sync API"). A
// verified program makes no instance: the gate refuses `new API`, a
// constructor no view lists (run under Node: the request pops).
import { API } from "typescript/unstable/sync";

export function wrong(xs: number[], config: string): number {
  const api = new API({
    fs: {
      getAccessibleEntries: (_path: string) => ({
        files: [],
        directories: [],
        toJSON: () => {
          xs.pop();
          return { files: [], directories: [] };
        },
      }),
    },
  });
  try {
    api.updateSnapshot({ openProject: config });
  } finally {
    api.close();
  }
  return xs.length;
}
