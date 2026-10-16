// A method read off its object, to be stored on another, is no function
// value: it takes the object it is read from as its receiver.
class Receiver {
  text: string = "ok";
  size(): number {
    return this.text.length;
  }
}

export function reattach(r: Receiver): number {
  const carrier = { text: "other", size: r.size };
  return carrier.size();
}
