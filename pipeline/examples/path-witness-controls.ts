type Value =
  | { readonly kind: "text"; readonly text: string }
  | { readonly kind: "empty" };
type Holder = { value: Value; other: Value };

export function primitiveBefore(holder: { value: { flag?: boolean } }): number {
  if (holder.value.flag) return 1;
  return 0;
}

export function primitiveAfterCall(
  holder: { value: { flag?: boolean } },
  replace: () => void,
): number {
  if (holder.value.flag) {
    replace();
    return 0;
  }
  return 0;
}

export function before(holder: Holder): number {
  if (holder.value.kind === "text") return 1;
  return 0;
}

export function receiver(holder: Holder, other: Holder): number {
  if (holder.value.kind === "text") {
    if (other.value.kind === "text") return 1;
  }
  return 0;
}

export function field(holder: Holder): number {
  if (holder.value.kind === "text") {
    if (holder.other.kind === "text") return 1;
  }
  return 0;
}

export function afterCall(holder: Holder, replace: () => void): number {
  if (holder.value.kind === "text") {
    replace();
    return 0;
  }
  return 0;
}

export function afterRoot(first: Holder, second: Holder): number {
  let holder = first;
  if (holder.value.kind === "text") {
    holder = second;
    return 0;
  }
  return 0;
}

export function backEdge(first: Holder, second: Holder, limit: number): number {
  let holder = first;
  if (holder.value.kind !== "text") return 0;
  let n = 0;
  while (n < limit) {
    n = n + 1;
    holder = second;
  }
  return n;
}

export function loop(holder: Holder, limit: number): number {
  if (holder.value.kind === "text") {
    let n = 0;
    while (n < limit) n++;
    return 0;
  }
  return 0;
}

export function caught(holder: Holder): number {
  try {
    if (holder.value.kind === "text") throw 1;
    return 0;
  } catch {
    return /* caught */ 0;
  }
}

export function afterCallRead(holder: Holder, replace: () => void): Value {
  if (holder.value.kind === "text") {
    replace();
    return holder.value;
  }
  return holder.value;
}

export function numericChain(holder: {
  value: { size: number; flag?: boolean };
}): number {
  if (holder.value.size && holder.value.flag && holder.value.flag) return 1;
  return 0;
}
