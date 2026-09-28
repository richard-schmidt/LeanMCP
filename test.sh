#!/data/data/com.termux/files/usr/bin/bash
# Unit tests always; the real-Lean integration + protocol tests with --integration.
# Each suite's exit status is checked on its own -- never through a pipe.
set -u
cd "$(dirname "$0")"
status=0
log="$(mktemp)"
run() {
  if python3 -m unittest -v "$1" >"$log" 2>&1; then
    tail -3 "$log"
  else
    cat "$log"; status=1
  fi
}
run tests.test_core
run tests.test_bridge_core
[ "${1:-}" = "--integration" ] && run tests.test_integration
rm -f "$log"
if [ $status -eq 0 ]; then echo "PASSED"; else echo "FAILED"; fi
exit $status
