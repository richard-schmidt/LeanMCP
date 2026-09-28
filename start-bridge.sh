#!/data/data/com.termux/files/usr/bin/bash
# Start the bridge unless it already answers. Idempotent: safe to run on every app launch.
#
#   start-bridge.sh            run it in the foreground (what the app's Termux
#                              RUN_COMMAND does: the Termux task stays alive, and
#                              keeps Termux alive, as long as the bridge runs)
#   start-bridge.sh --detach   start it detached from this shell, then return
#   start-bridge.sh --pair     also send the pairing link to the app first
#
# The log goes to $TMPDIR/bridge.log. A second copy started in a race loses the
# port bind and exits; the Lean server is started lazily, so it leaves nothing behind.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
PORT=8766
detach=0; pair=0
for a in "$@"; do
  case "$a" in
    --detach) detach=1 ;;
    --pair) pair=1 ;;
    *) echo "usage: start-bridge.sh [--detach] [--pair]" >&2; exit 2 ;;
  esac
done

export PATH="$HOME/.elan/termux-shims:$HOME/.elan/bin:$PATH"
LOG="${TMPDIR:-$PREFIX/tmp}/bridge.log"

if [ $pair -eq 1 ]; then python3 "$HERE/bridge.py" --port $PORT --pair || exit 1; fi

if "$PREFIX/bin/curl" -s -m 2 -o /dev/null "http://127.0.0.1:$PORT/v1/health"; then
  echo "bridge already up on 127.0.0.1:$PORT"
  exit 0
fi

cd "$HERE"
if [ $detach -eq 1 ]; then
  setsid nohup python3 bridge.py --port $PORT >> "$LOG" 2>&1 < /dev/null &
  echo "bridge starting (log: $LOG)"
  exit 0
fi
echo "bridge starting in the foreground (log: $LOG)"
exec python3 bridge.py --port $PORT >> "$LOG" 2>&1 < /dev/null
