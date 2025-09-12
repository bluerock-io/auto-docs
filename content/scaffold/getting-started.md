---
title: Getting Started
no_code: true
eleventyNavigation:
    parent: scaffold
    order: 0
---

The `scaffold` tool offers a quick way to start verifying existing C++ code.

## Requirements

The tutorial assumes that the following tools are installed:

* BlueRock proof automation
* `scaffold`
* [`bear`](https://github.com/rizsotto/Bear)
* [`clang`](https://clang.llvm.org/)

## The C++ Code

To start with `scaffold`, we create a fresh directory `example/` and populate it with C++
code. We start with a very simple `swap` function which we put into `example/src/stage1.cpp`.

```cpp
#include <cstddef>

void swap(size_t& x, size_t& y) {
    size_t tmp = y;
    y = x;
    x = tmp;
}
```

Before we start verifying the code, we have to make sure `scaffold` knows how to
build it. `scaffold` uses the standard
[compile_commands.json](https://clang.llvm.org/docs/JSONCompilationDatabase.html)
format to determine how to build your code. Since we have a simple project, we will generate a `compile_commands.json` using the [`bear` tool](https://github.com/rizsotto/Bear).

```shell
$ bear -- clang -c src/stage1.cpp
```

::: info
Build systems such as [cmake](https://cmake.org/cmake/help/latest/variable/CMAKE_EXPORT_COMPILE_COMMANDS.html) and [bazel](https://github.com/kiron1/bazel-compile-commands) support generating `compile_commands.json` files.
:::

## Project Initialization

Before we get to verification, we have to prepare our project.
To do this, we run `scaffold init`, which presents us with a number of prompts to configure the project. For this example, we can accept the defaults by pressing **Enter**.

```shell
$ scaffold init
> Project name? example
> Rocq name? example
> Proof directory? proof
> Initialization complete!
Shall I generate the build files? Yes
Using compilation database! /home/janno/br/bhv/fmdeps/fm-tools/scaffold/example/compile_commands.json
```

`scaffold init` creates all files necessary for our verification endeavour.
Accordingly, `example/` now contains a number of new directories and files. We
will not have to make changes to any of the files and thus do need to inspect
them at this point. We include the directory listing below to allow readers to
check that their local state matches the tutorial.

```shell
$ tree
.
├── br-project.toml
├── compile_commands.json
├── dune
├── dune-project
├── proof
│   ├── dune
│   └── prelude
│       ├── proof.v
│       └── spec.v
├── src
│   ├── dune
│   ├── dune.inc
│   └── stage1.cpp
└── stage1.o
```

## Building the Project

It is useful to confirm that the generated code builds. To do that, we use [`dune`](https://dune.build/).

```shell
$ dune build
```

What this command does is use the rules that `scaffold` generated to convert all of the C++ code that you have into a form that BRiCk can understand it.
This process relies on the build files generated in the previous step, when you answered **Yes** to "Shall I generate the build files?".
If you ever add or remove C++ files from your project such that your `compile_commands.json` file needs to change, you will need to regenerate these build files.
You can do this using `scaffold gen`.

```shell
$ scaffold gen
```

## Wrapping Up

At this point, we have initialized a new verification of a simple bit of C++ code.
To continue with this example, take a look at:

1. [Specifying functions](default-specs.md)
2. [Adapting function specifications](by_hand.md)

