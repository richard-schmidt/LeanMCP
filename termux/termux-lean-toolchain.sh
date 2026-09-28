#!/data/data/com.termux/files/usr/bin/bash
# Install an official Lean 4 toolchain into elan on Termux (aarch64, bionic).
#
# Usage: termux-lean-toolchain.sh v4.35.0-rc2      (tag from a lean-toolchain file)
#        termux-lean-toolchain.sh --repatch v4.35.0-rc2   (re-patch an installed one)
#
# Why this exists: elan is static and cannot resolve DNS on Android, so
# `elan toolchain install` fails. Upstream binaries also expect
# /lib/ld-linux-aarch64.so.1. This script downloads with Termux curl, points every
# ELF at Termux's glibc loader (pkg glibc-runner), and wraps ld.lld so executables
# Lake links (e.g. Mathlib's `cache`) get the same loader.
# Pair with ~/.elan/termux-shims on PATH: Lake exports LD_LIBRARY_PATH to the
# toolchain's glibc libs, which breaks bionic curl/git spawned from inside Lake.
set -euo pipefail

repatch=0
if [ "${1:-}" = "--repatch" ]; then repatch=1; shift; fi
tag="${1:?usage: $0 [--repatch] vX.Y.Z[-rcN]}"
ver="${tag#v}"
G="$PREFIX/glibc/lib"
T="$HOME/.elan/toolchains/leanprover--lean4---$tag"

[ -x "$G/ld-linux-aarch64.so.1" ] || { echo "missing $G/ld-linux-aarch64.so.1: pkg install glibc-runner" >&2; exit 1; }

if [ $repatch -eq 0 ]; then
  [ -e "$T" ] && { echo "$T already exists (use --repatch)" >&2; exit 1; }
  tmp="$(mktemp -d "$PREFIX/tmp/lean-XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT
  url="https://github.com/leanprover/lean4/releases/download/$tag/lean-$ver-linux_aarch64.tar.zst"
  echo "downloading $url"
  curl -fSL --progress-bar -o "$tmp/lean.tar.zst" "$url"
  tar --use-compress-program=unzstd -xf "$tmp/lean.tar.zst" -C "$tmp"
  mkdir -p "$(dirname "$T")"
  mv "$tmp/lean-$ver-linux_aarch64" "$T"
fi

for f in "$T"/bin/*; do
  [ -f "$f" ] || continue
  readelf -l "$f" 2>/dev/null | command grep -q 'program interpreter' || continue
  rp="$(patchelf --print-rpath "$f")"
  case "$rp" in *"$G"*) ;; *) rp="${rp:+$rp:}$G" ;; esac
  patchelf --set-interpreter "$G/ld-linux-aarch64.so.1" --set-rpath "$rp" "$f"
done

if [ ! -e "$T/bin/ld.lld.real" ]; then
  mv "$T/bin/ld.lld" "$T/bin/ld.lld.real"
  cat > "$T/bin/ld.lld" <<EOF
#!/data/data/com.termux/files/usr/bin/sh
# Termux: point every linked executable at Termux's glibc loader, not /lib/ld-linux-aarch64.so.1.
exec "\$(dirname "\$0")/ld.lld.real" -flavor gnu "\$@" --dynamic-linker=$G/ld-linux-aarch64.so.1 -rpath $G
EOF
  chmod +x "$T/bin/ld.lld"
fi

S="$HOME/.elan/termux-shims"
mkdir -p "$S"
for t in curl git; do
  cat > "$S/$t" <<EOF
#!/data/data/com.termux/files/usr/bin/sh
# Lake exports LD_LIBRARY_PATH=<toolchain glibc libs>; bionic tools must not see it.
unset LD_LIBRARY_PATH
exec $PREFIX/bin/$t "\$@"
EOF
  chmod +x "$S/$t"
done

# Lean's server watchdog (`lake serve`) dies without a TZif file, and Android has no
# /etc/localtime or zoneinfo dir. Unpack the pure-Python tzdata wheel's TZif files;
# LSP clients then set TZ=<absolute path to a zone file> for the server only.
Z="$HOME/.local/share/zoneinfo"
if [ ! -f "$Z/UTC" ]; then
  tz="$(mktemp -d "$PREFIX/tmp/tz-XXXXXX")"
  pip download -q --no-deps tzdata -d "$tz"
  unzip -q "$tz"/tzdata-*.whl -d "$tz/x"
  mkdir -p "$(dirname "$Z")"
  cp -r "$tz/x/tzdata/zoneinfo" "$Z"
  find "$Z" \( -name '__init__.py' -o -name '__pycache__' \) -prune -exec rm -rf {} +
  rm -rf "$tz"
fi

"$T/bin/lean" --version
"$T/bin/lake" --version
