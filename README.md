# Symbology Normalization (symbologyl2)

## Introduction

Utility functions for parsing, normalizing, and translating between various
capital market symbology types.

## Current Support

- [x] US equities
  - [x] CMS Concatenated/Suffix
  - [x] Nasdaq Integrated
  - [x] CQS (NYSE/CTA plan)

## Development

```
cargo clippy --all-features --all-targets -- -D warnings
cargo test --all
cargo build --release
```
