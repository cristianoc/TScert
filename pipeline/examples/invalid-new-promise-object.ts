// Resolving a promise with an object adopts it when it is a thenable, and a
// record may be one: `new Promise`'s `resolve` is stated at a primitive, as
// an async function's return is, though TypeScript admits any value.
type Box = { value: number };

function boxed(): Promise<Box> {
  return new Promise<Box>(
    (resolve: (value: Box) => void, reject: (reason: unknown) => void) => {
      resolve({ value: 1 });
    },
  );
}
