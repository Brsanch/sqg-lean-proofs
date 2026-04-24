---
name: Build / toolchain issue
about: `lake build` fails, paper won't render, or CI acts up
title: "[build] "
labels: build
---

## What failed

<!-- e.g. "lake build fails", "scripts/build-paper.sh errors out",
     "CI Lean Action workflow times out". -->

## Environment

- OS and version:
- Lean / elan version (`lean --version`, `elan --version`):
- Mathlib version (`lake-manifest.json` → mathlib rev):
- If paper build: pandoc version (`pandoc --version`) and TeX engine:

## Steps to reproduce

```bash
# exact commands
```

## Log output

<!-- The last 30-50 lines of the failing build output, in a code block.
     If it's a hang rather than a failure, state the CPU and memory
     usage at the point of hang. -->

## Workaround tried

<!-- If any. -->
