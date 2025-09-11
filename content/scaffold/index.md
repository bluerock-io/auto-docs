---
title: Scaffold
permalink: /scaffold/
no_code: true
eleventyNavigation:
    key: scaffold
    title: Scaffold
    order: 40
---

The `scaffold` tool is a **highly-opinionated** tool for verifying C++ code using the BRiCk ecosystem.
You can think of it as a verification-focused version of tools such as `cargo`, `npm`, or `dune`.

`scaffold` currently provides infrastructure for
* [Bootstrapping a verification project](getting-started.md) by setting up dependencies, and establishing best-practices file layouts that mirror your C++ code.
* [Bootstrapping a function specification and verification](default-specs.md)

### Design Philosophy

`scaffold` aims to be a highly extensible system that can be used throughout the lifetime of your verification while retaining the **flexibility of working with the full power of BRiCk**.

### 💭 Have Ideas?
Do you have ideas for extending `scaffold`? Let us know!
