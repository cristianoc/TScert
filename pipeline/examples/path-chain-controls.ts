// Accepted neighbours for forged witnesses of a path of two members
// (HOST-FAMILIES.md, "Entries"): each entry's witness of `holder.mid.leaf`
// is read from the witness of `holder.mid` through `leaf`. The forged
// documents of `pipeline/test.mts` change one thing each: the second
// segment's receiver, its field, the predecessor an entry claims it from,
// and a call between the test and the entry.
type Leaf =
  | { readonly kind: "text"; readonly text: string }
  | { readonly kind: "empty" };
type Mid = { readonly leaf: Leaf; readonly other: Leaf };
type Holder = { readonly mid: Mid; readonly alt: Mid };

export function before(holder: Holder): number {
  if (holder.mid.leaf.kind === "text") return 1;
  return 0;
}

export function receiver(holder: Holder): number {
  if (holder.mid.leaf.kind === "text") {
    if (holder.alt.leaf.kind === "text") return 1;
  }
  return 0;
}

export function field(holder: Holder): number {
  if (holder.mid.leaf.kind === "text") {
    if (holder.mid.other.kind === "text") return 1;
  }
  return 0;
}

export function afterCall(holder: Holder, replace: () => void): number {
  if (holder.mid.leaf.kind === "text") {
    replace();
    return 0;
  }
  return 0;
}

export function read(holder: Holder): string {
  if (holder.mid.leaf.kind !== "text") return "";
  return holder.mid.leaf.text;
}
