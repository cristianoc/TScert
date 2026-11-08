// The DOM operations a span is measured with run no code of the program's: a
// program defines no custom element, whose reactions an insertion would run.
// A definition is refused. Under Node with stand-ins, the element's
// `connectedCallback` empties the array its caller then reads.
export function first(parent: Element): number {
  const seen: number[] = [1]
  customElements.define('x-pop', class extends HTMLElement {
    connectedCallback(): void { seen.pop() }
  })
  parent.appendChild(document.createElement('span'))
  return seen[0]!
}
