// A named union with a falsy primitive retains that value through &&.
type Receiver = false | { readonly value: string };

export function signature(receiver: Receiver): string {
  return receiver && "printed";
}
