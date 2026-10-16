// A literal cannot gain a Boolean index view when one allocated value is a string.
function badDictionary(): { readonly [key: string]: boolean } {
  return { ready: true, label: "not boolean" };
}
