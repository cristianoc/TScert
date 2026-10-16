// An async function settling to an object: JavaScript would adopt it if it
// had a `then`, its own or one on its prototype, and the model settles an
// async result to a primitive.
export async function make(): Promise<{ n: number }> {
  return { n: 1 };
}
