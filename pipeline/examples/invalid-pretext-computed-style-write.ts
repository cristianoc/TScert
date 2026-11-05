// Boundary: computed style cannot satisfy the inline-style setter's host contract.
export function write(element: Element): void {
  getComputedStyle(element).cssText = 'color:red'
}
