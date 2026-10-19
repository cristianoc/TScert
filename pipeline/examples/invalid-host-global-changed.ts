// The project declares `clearTimeout(timeout: number)`, an overload whose
// text is not the one reviewed for Node's: the pin fails and the call is
// refused, never read at the declaration.
export function stop(id: number): void {
  clearTimeout(id);
}
