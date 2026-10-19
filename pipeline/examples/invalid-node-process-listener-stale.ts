// A listener runs after the unit returns, between jobs: a narrowing made
// when it was registered says nothing of the captured box then (run under
// Node: the field is `undefined` at exit). Its body reads the field at its
// declared type.
export function register(box: { v: number | undefined }): void {
  if (box.v === undefined) return;
  process.on("exit", () => {
    const n: number = box.v;
    void n.toFixed();
  });
}
