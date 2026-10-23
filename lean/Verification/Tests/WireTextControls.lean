import Verification.Source.RequestCli

/-! Controls for the scan of a wire text's strings for lone surrogate
escapes (REQUEST-PROTOCOL.md, "Wire text"), which runs before Lean's JSON
parser, which would read a lone surrogate as U+FFFD. Each text is the JSON
text itself, so `\\` below is one backslash of it. -/
namespace Verification.WireTextControls
open RequestCli

-- A lone high surrogate, a lone low one, and a high one before another escape.
#guard (loneSurrogate "\"\\ud800\"".toList).isSome
#guard (loneSurrogate "\"\\uDC00\"".toList).isSome
#guard (loneSurrogate "\"\\ud800\\u0041\"".toList).isSome
-- A pair, in lower and in upper case hexadecimal digits.
#guard (loneSurrogate "\"\\ud83d\\ude00\"".toList).isNone
#guard (loneSurrogate "\"\\uD83D\\uDE00\"".toList).isNone
-- An escaped backslash before `u` escapes nothing: the string is a
-- backslash and the letters `ud800`.
#guard (loneSurrogate "\"\\\\ud800\"".toList).isNone
-- An escaped quote does not end the string: the escape after it is read.
#guard (loneSurrogate "\"\\\"\\ud800\"".toList).isSome
-- Outside a string nothing is an escape, and a closed string ends one.
#guard (loneSurrogate "[\"a\", \"\\u00e9\"]".toList).isNone

end Verification.WireTextControls
