#!/bin/sh
# The C compiler `make build-lean` gives Lake (LEAN_CC): the Lean toolchain's
# clang, which compiles the C that Lean generates for the verifier. Lean's
# elaboration bounds the build's wall-clock time: each module waits for the
# modules it imports. No module waits for compiled C, only the final link.
# On macOS clang therefore runs at utility priority and leaves the performance
# cores to elaboration.
cc="$TSCERT_LEAN_SYSROOT/bin/clang"
if [ -x /usr/sbin/taskpolicy ]; then exec /usr/sbin/taskpolicy -c utility "$cc" "$@"; fi
exec "$cc" "$@"
