// An async body resolving a number is not a `Promise<string>`.
export function bad(): { fn: () => Promise<string> } {
  return { fn: async () => 1 };
}
