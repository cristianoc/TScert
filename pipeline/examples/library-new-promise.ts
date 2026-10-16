// `new Promise(executor)` calls the executor at once with the promise's
// resolving functions (`%NewPromise%`): resolving settles the promise to a
// primitive; rejecting, or a throw out of the executor, makes it reject.
function resolved(): Promise<number> {
  return new Promise<number>(
    (resolve: (value: number) => void, reject: (reason: unknown) => void) => {
      resolve(0);
    },
  );
}

function rejected(): Promise<string> {
  return new Promise(
    (resolve: (value: string) => void, reject: (reason: unknown) => void) => {
      reject("no");
    },
  );
}

async function awaited(): Promise<boolean> {
  const b = await new Promise(
    (resolve: (value: boolean) => void, reject: (reason: unknown) => void) => {
      resolve(true);
    },
  );
  return b;
}
