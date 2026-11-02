// A call can replace the member whose old value the logical chain tested.
// Node observes undefined at the promised string return.
type Holder = { value: { size: number; text?: string | undefined } };
export function wrong(holder: Holder, change: () => void): string {
  if (holder.value.text && holder.value.size && (change(), true))
    return holder.value.text;
  return "";
}
