// A `finally` callback returning an object whose `then` is callable: the
// native `finally` resolves the cleanup result before forwarding, calling
// that `then` (run under Node: `log` holds 1 once the result settles).
export function cleanup(p: Promise<number>, log: number[]): Promise<number> {
  return p.finally(() => ({
    then(resolve: () => void): void {
      log.push(1);
      resolve();
    },
  }));
}
