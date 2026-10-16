interface Receiver {
  accept<T extends Promise<number | string>>(value: T): number;
}

// Covariance preserves the element constraint; boolean is outside the bound.
export function outsideBound(
  receiver: Receiver,
  value: Promise<boolean>,
): number {
  return receiver.accept(value);
}
