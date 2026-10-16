interface Receiver {
  accept<T extends Promise<number | string>>(value: T): number;
}

// The method's bound and ordinary widening ask for the same inclusion.
export function directBound(
  receiver: Receiver,
  value: Promise<number>,
): number {
  return receiver.accept(value);
}

export function widenedBound(
  receiver: Receiver,
  value: Promise<number>,
): number {
  const widened: Promise<number | string> = value;
  return receiver.accept(widened);
}
