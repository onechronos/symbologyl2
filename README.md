[![release build](https://github.com/onechronos/symbologyl2/actions/workflows/build.yml/badge.svg)](https://github.com/onechronos/symbologyl2/actions/workflows/build.yml)
[![format + lint + test](https://github.com/onechronos/symbologyl2/actions/workflows/test.yml/badge.svg)](https://github.com/onechronos/symbologyl2/actions/workflows/test.yml)
[![Coverage Status](https://coveralls.io/repos/github/onechronos/symbologyl2/badge.svg)](https://coveralls.io/github/onechronos/symbologyl2)
[![Docs](https://img.shields.io/docsrs/symbologyl2)](https://docs.rs/symbologyl2/)
[![Crates.io](https://img.shields.io/crates/v/symbologyl2)](https://crates.io/crates/symbologyl2)

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
