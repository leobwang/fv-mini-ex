# Pinned toolchains

| Tool | Version | Source |
|---|---|---|
| Lean | 4.32.0 | `lean/lean-toolchain` (elan) |
| Mathlib | v4.32.0 (rev `81a5d257c8e410db227a6665ed08f64fea08e997`) | `lean/lake-manifest.json` |
| Dafny | 4.11.0 | GitHub release `v4.11.0`; sha256 per platform in `tools/setup.sh` |
| Verus | 0.2026.09.27.3cf1832 (bundled Z3 4.16.0) | GitHub release `release/0.2026.09.27.3cf1832`; sha256 in `tools/setup.sh` |
| Rust (for Verus) | 1.98.1 | rustup |
| Python (checker) | ≥ 3.8, stdlib only | system |

| Platform | Status |
|---|---|
| Linux x86-64 | all solutions verified 2026-10-24 |
| macOS arm64 | not yet verified: run `tools/setup.sh && ./check --solutions` once and record the result here |
