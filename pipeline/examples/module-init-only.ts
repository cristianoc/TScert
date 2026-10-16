// A module whose only code is its initialization is checked through that
// unit: constants, a class with a method, construction and a call, in order.
const base: number = 40;
const answer = base + 2;
class Counter {
  count: number = answer;
  next(): number {
    return this.count + 1;
  }
}
const counter = new Counter();
const after: number = counter.next();
counter.next();
