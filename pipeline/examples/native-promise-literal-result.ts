export async function direct(): Promise<"hello"> {
  return "hello";
}

export function arrow(): Promise<1> {
  const f = async (): Promise<1> => 1;
  return f();
}

export function field(): Promise<"hello"> {
  const x: { fn: () => Promise<"hello"> } = { fn: async () => "hello" };
  return x.fn();
}

export function resolved(): Promise<"hello"> {
  return Promise.resolve("hello");
}
