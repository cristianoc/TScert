// A closure literal without a result annotation, expected at one signature,
// is claimed at that signature's result where its body's fits it: a literal
// result the context asks for, and an async body's promise.
export function literal(): () => "hello" {
  const x: { fn: () => "hello" } = { fn: () => "hello" };
  return x.fn;
}

export function asyncField(): { fn: () => Promise<string> } {
  return { fn: async () => "hello" };
}

export function asyncBlock(): { fn: () => Promise<number> } {
  return {
    fn: async () => {
      return 1;
    },
  };
}
