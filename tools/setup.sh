#!/bin/sh
# Install the pinned toolchains into .toolchain/ (Linux x86-64 or macOS arm64/x86-64).
#
#   tools/setup.sh            install everything that is missing
#   tools/setup.sh --check    only report what is installed
#
# If tools/local-paths (git-ignored) names an existing install of the pinned
# version, setup links to it instead of downloading. Every download is checked
# against the sha256 that GitHub publishes for the release asset.
# POSIX sh on purpose: macOS ships bash 3.2.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TC="$ROOT/.toolchain"
CHECK_ONLY=0
[ "${1:-}" = "--check" ] && CHECK_ONLY=1

DAFNY_VER=4.11.0
VERUS_VER=0.2026.09.27.3cf1832
VERUS_RUST=1.98.1
LEAN_TOOLCHAIN=$(cat "$ROOT/lean/lean-toolchain")

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    DAFNY_ASSET=dafny-$DAFNY_VER-x64-ubuntu-22.04.zip
    DAFNY_SHA=a46a9ff7cdd720f7955854c78e95df13f4cfe6b80691b05f8654fe19e8267179
    VERUS_ASSET=verus-$VERUS_VER-x86-linux.zip; VERUS_DIR=verus-x86-linux
    VERUS_SHA=43814031e10df043221d83c7fa842e3ebd662cb7b0090fc1eb4d7a8673226978 ;;
  Darwin-arm64)
    DAFNY_ASSET=dafny-$DAFNY_VER-arm64-macos-13.zip
    DAFNY_SHA=c90c75e7d5db9c6ccbb7127840dfe43f0ac938b039a7ebed146d8ead383a572f
    VERUS_ASSET=verus-$VERUS_VER-arm64-macos.zip; VERUS_DIR=verus-arm64-macos
    VERUS_SHA=14ae529ef84178dd6b6debac76dd093803fcfd01123023561e19ac1575e53b83 ;;
  Darwin-x86_64)
    DAFNY_ASSET=dafny-$DAFNY_VER-x64-macos-13.zip
    DAFNY_SHA=5fc0de946c5b2fad33f16bd22a5b06f4fd0dfa7f6d770284237e3f1f3ca9f73d
    VERUS_ASSET=verus-$VERUS_VER-x86-macos.zip; VERUS_DIR=verus-x86-macos
    VERUS_SHA=c304fd8fe2eb143cc5a615461fb37b17f00d2387d6054ec013717eb056c0b0ff ;;
  *) echo "unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac

DAFNY_LOCAL=""; VERUS_LOCAL=""; MATHLIB_LOCAL=""
# shellcheck disable=SC1091
[ -f "$ROOT/tools/local-paths" ] && . "$ROOT/tools/local-paths"

say() { printf '%s\n' "$*"; }
sha256() { if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }

fetch() {  # fetch <url> <sha256> <dest-zip>
  say "  downloading $1"
  curl -fL --progress-bar -o "$3" "$1"
  got=$(sha256 "$3")
  if [ "$got" != "$2" ]; then echo "sha256 mismatch for $3: got $got, want $2" >&2; rm -f "$3"; exit 1; fi
}

unquarantine() { [ "$(uname -s)" = Darwin ] && xattr -dr com.apple.quarantine "$1" 2>/dev/null || true; }

mkdir -p "$TC"

# ---- Dafny: .toolchain/dafny -> directory containing the `dafny` executable
if [ -x "$TC/dafny/dafny" ]; then
  say "dafny: $("$TC/dafny/dafny" --version)"
elif [ $CHECK_ONLY = 1 ]; then
  say "dafny: MISSING"
elif [ -n "$DAFNY_LOCAL" ] && [ -x "$DAFNY_LOCAL/dafny" ]; then
  ln -sfn "$DAFNY_LOCAL" "$TC/dafny"; say "dafny: linked $DAFNY_LOCAL"
else
  fetch "https://github.com/dafny-lang/dafny/releases/download/v$DAFNY_VER/$DAFNY_ASSET" "$DAFNY_SHA" "$TC/$DAFNY_ASSET"
  rm -rf "$TC/dafny-$DAFNY_VER"; mkdir -p "$TC/dafny-$DAFNY_VER"
  unzip -q "$TC/$DAFNY_ASSET" -d "$TC/dafny-$DAFNY_VER"; rm "$TC/$DAFNY_ASSET"
  unquarantine "$TC/dafny-$DAFNY_VER"
  ln -sfn "$TC/dafny-$DAFNY_VER/dafny" "$TC/dafny"; say "dafny: installed $DAFNY_VER"
fi

# ---- Verus: .toolchain/verus -> directory containing the `verus` executable
if [ -x "$TC/verus/verus" ]; then
  say "verus: $("$TC/verus/verus" --version 2>&1 | sed -n 's/.*Version: //p')"
elif [ $CHECK_ONLY = 1 ]; then
  say "verus: MISSING"
elif [ -n "$VERUS_LOCAL" ] && [ -x "$VERUS_LOCAL/verus" ]; then
  ln -sfn "$VERUS_LOCAL" "$TC/verus"; say "verus: linked $VERUS_LOCAL"
else
  fetch "https://github.com/verus-lang/verus/releases/download/release/$VERUS_VER/$VERUS_ASSET" "$VERUS_SHA" "$TC/$VERUS_ASSET"
  rm -rf "$TC/verus-$VERUS_VER"; mkdir -p "$TC/verus-$VERUS_VER"
  unzip -q "$TC/$VERUS_ASSET" -d "$TC/verus-$VERUS_VER"; rm "$TC/$VERUS_ASSET"
  unquarantine "$TC/verus-$VERUS_VER"
  ln -sfn "$TC/verus-$VERUS_VER/$VERUS_DIR" "$TC/verus"; say "verus: installed $VERUS_VER"
fi
if command -v rustup >/dev/null; then
  if rustup toolchain list | grep -q "^$VERUS_RUST"; then say "rust $VERUS_RUST: ok"
  elif [ $CHECK_ONLY = 1 ]; then say "rust $VERUS_RUST: MISSING (verus needs it)"
  else rustup toolchain install "$VERUS_RUST"; fi
else
  say "rustup: MISSING (verus needs Rust $VERUS_RUST; install from https://rustup.rs)"
fi

# ---- Lean + Mathlib: elan reads lean/lean-toolchain; Mathlib goes in lean/.lake
if ! command -v lake >/dev/null && [ ! -x "$HOME/.elan/bin/lake" ]; then
  say "elan: MISSING (install: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh)"
  [ $CHECK_ONLY = 1 ] || exit 1
else
  PATH="$HOME/.elan/bin:$PATH"
  if [ -d "$ROOT/lean/.lake/packages/mathlib/.lake/build/lib" ]; then
    say "lean: $LEAN_TOOLCHAIN, mathlib: present"
  elif [ $CHECK_ONLY = 1 ]; then
    say "lean: $LEAN_TOOLCHAIN, mathlib: MISSING"
  elif [ -n "$MATHLIB_LOCAL" ] && [ -d "$MATHLIB_LOCAL/packages/mathlib" ]; then
    say "mathlib: copying local build from $MATHLIB_LOCAL"
    mkdir -p "$ROOT/lean/.lake"; cp -R "$MATHLIB_LOCAL/packages" "$ROOT/lean/.lake/"
  else
    say "mathlib: fetching sources and prebuilt cache (several GB)"
    (cd "$ROOT/lean" && lake exe cache get)
  fi
  # physlib has no prebuilt cache. Build just the modules the exercises import (and
  # their dependencies), once; a rerun is a quick no-op.
  PL_MODS=$(grep -rhoE '^import (Physlib|QuantumInfo)[A-Za-z0-9_.]*' \
    "$ROOT/lean/easy" "$ROOT/lean/medium" "$ROOT/lean/hard" | sort -u | sed 's/^import //')
  PL_OUT="$ROOT/lean/.lake/packages/physlib/.lake/build/lib/lean"
  PL_MISSING=""
  for m in $PL_MODS; do
    [ -f "$PL_OUT/$(printf '%s' "$m" | tr . /).olean" ] || PL_MISSING="$PL_MISSING +$m"
  done
  if [ -z "$PL_MISSING" ]; then
    say "physlib: built ($(printf '%s\n' $PL_MODS | wc -l | tr -d ' ') modules used by the exercises)"
  elif [ $CHECK_ONLY = 1 ]; then
    say "physlib: NOT BUILT ($(printf '%s\n' $PL_MISSING | wc -l | tr -d ' ') modules missing)"
  else
    say "physlib: building the modules the exercises import (one-time; 10-20 minutes)"
    # shellcheck disable=SC2086
    (cd "$ROOT/lean" && lake build $PL_MISSING)
  fi
fi

[ $CHECK_ONLY = 1 ] || say "done. Try: ./check lean E01"
