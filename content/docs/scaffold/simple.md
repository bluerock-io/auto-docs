---
title: A Simple Verification Example with `scaffold`
no_code: true
---

The `scaffold` tool offers a quick way start verification of existing C++ code.
In this tutorial, we look at some of the features of the tool in a series of
simple examples.

## Requirements

The tutorial assumes that the following tools are installed:

* `scaffold`
* `bear`
* `clang`
* BlueRock proof automation

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
build it. To keep the example simple, we do not use a build system. Instead, we
build the file manually and use `bear` to automatically put the build
instructions into a file called `compile_commands.json` where `scaffold` can
find them. To this end, we run the following command in `example/`.

```shell
$ bear -- clang -c src/stage1.cpp
```

In a real world example, the invocation of `clang` would be replaced by an
invocation of `cmake` or something similar. For our simple example, calling
`clang` directly suffices and we can now run `scaffold` for the first time to
start verifying our code.

## Project Initialization

Before we get to that, we first have to prepare our project for verification. To
this end, we run `scaffold init`, which presents us with a number of prompts for which
we accept the default answers by pressing **Enter**.

```shell
$ scaffold init
> Project name? example
> Rocq name? example
> Proof directory? proof
> Initialization complete!
Shall I generate the build files? Yes
Using compilation database! /home/janno/br/bhv/fmdeps/fm-tools/scaffold/example/compile_commands.json
```

Note that build files can always be generated separately by running `scaffold gen`.

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
    ├── dune
    ├── dune.inc
    └── stage1.cpp
└── stage1.o
```

With the project initialized, we can move on to the actual verification task.

## Verification

`scaffold` is geared towards incremental verification. It allows users to
iteratively increase the scope of the verification project. Running the
interactive command `scaffold verify` presents us with all available
specification/verification targets (or, in our case, one target), e.g.
functions, but also `enum`s and `struct`s. Run `scaffold verify`,
make sure the `swap` function is selected, and confirm with **Enter**.

```shell
$ scaffold verify
? What would you like to specify?  
>    swap(size_t &, size_t &) @ src/stage1.cpp
  <DONE>
```

`scaffold` now asks us to select **how** we want to specify the function. We
have the option of writing a specification by hand, to automatically generate a
default specification to verify {{ "memory safety" | terminology }} of `swap`, or to
sidestep the task of specifying `swap` by indicating that the verification of
clients should inline the function. To keep the example simple, we select `Memory safey`.

```shell
Verifying swap(size_t &, size_t &)...
void swap(size_t& x, size_t& y) {
    size_t tmp = y;
    y = x;
    x = tmp;
}
? How?  
  By hand
> Memory safety
  Inline it
[Write a specification for the function]
```

We are brought back to the initial overview where `swap` is now marked with a
checkmark, indicating that `scaffold` knows what the function's specification is
supposed to be. We select `<DONE>` to save our changes to disk.

```shell
? What would you like to specify?  
  ✅ swap(size_t &, size_t &) @ src/stage1.cpp
> <DONE>
```

The `proof/` directory now contains a new directory called `stage1_cpp`. In it,
`scaffold` collects specifications and proofs of functions from `stage1.cpp`, i.e. `swap`
in our case.

```shell
$ tree proof/stage1_cpp/
proof/stage1_cpp/
├── pred.v
├── proof
│   └── swap.v
├── proof.v
└── spec.v
```

Two files are of particular interest to us. 
1. `proof/stage1_cpp/spec.v` contains the specification that was generated for us. Since we selected the default specification for {{ "memory safety" | terminology }}, we see only following line:
   ```coq
   cpp.spec "swap(size_t &, size_t &)" as swap_spec default.
   ```
   We will later see examples of explicit specifications which take the place of the `default` keyword.

2. `proof/stage1_cpp/proof/swap.v` contains a generated proof that verifies {{ "memory safety" | terminology }} of `swap`. The two relevant lines are:
   ```coq
   Lemma swap_ok : verify[source] "swap(size_t &, size_t &)".
   Proof. verify_spec; go. Qed.
   ```

Even though the proof ends with `Qed`, it has not actually been checked yet. We
can run `dune build proof/` (or `dune b proof/` for short) to check the proof is
indeed correct. The command should succeed.

```shell
$ dune b proof/
```

## What Have We Proven?

The default specification for {{ "memory safety" | terminology }} was generated
for us automatically and we have not had a chance to look at its contents. We
take a quick look behind the curtains to understand what it is we have proven
about `swap`. To do this, we modify `proof/stage1_cpp/spec.v`, adding `Print
swap_spec.` to the end of the file. Running `dune b proof/` to rebuild the file produces the
following output.

```coq
swap_spec =
λ (thread_info : biIndex) (_Σ : gFunctors) (Σ : cpp_logic thread_info _Σ) 
  (σ : genv),
  specify
    {|
      info_name := "swap(unsigned long&, unsigned long&)";
      info_type :=
        tFunction "void" ["unsigned long&"%cpp_type; "unsigned long&"%cpp_type]
    |}
    (\arg{(x_addr : ptr) (x : Z)} "x" (Vptr x_addr)
     \pre x_addr |-> ulongR 1$m x 
     \arg{(y_addr : ptr) (y : Z)} "y" (Vptr y_addr)
     \pre y_addr |-> ulongR 1$m y 
     \post    Exists (x0 x1 : Z), y_addr |-> ulongR 1$m x0 ** x_addr |-> ulongR 1$m x1)
```

We are interested in the specification term, which consists of the last 5 lines of the output.
These 5 lines can be categorized into three distinct groups:
1. Function argument specifiers of the form `\arg{(<name>_addr : ptr)} "<name>"
   (Vptr <name>_addr)`, where `<name>` is either `x` or `y` in our case. This
   syntax is quite concise and encompasses three somewhat separate things.
   1. By using curly braces after `\arg`, this specifier
      generalizes the rest of the specification over a verification variable
      called `<name>_addr`, providing us with a stand-in for the C++ reference `<name>`.
   2. It ties that variable to the respective argument of the function by name
      (i.e. through the string `"x"` or `"y"`, respectively).
   3. It then indicates that it expects the C++ value of that argument to be a
      pointer containing `<name>_addr` by specifying the pattern `(Vptr
      <name>_addr)`. The establishes the connection between our verification
      variables and the C++ state.

   In the example above, we additionally see `(x : Z)` and `(y : Z)` in curly
   braces. These are additional verification variables of integer type (written
   `Z` in Rocq) that come into play in the next specifier category.
2. Preconditions, written `\pre ...`. In our case, these preconditions are of
   the form `<name>_addr |-> ulongR 1$m <name>`. The `|->` operator is explained
   in more detail in the chapters on <a href="docs/state_basics/">Program
   State</a> and <a href="docs/primitive_reps/main">Primitive Data</a>. Here, it
   is sufficient to know that these preconditions specify the contents of our
   C++ references, establishing the connection between the C++ state (i.e. the
   memory to which our references point) and our verification variables `x` and
   `y`.
   
   Specifying multiple preconditions establishes a {{ "separating conjunction" |
   terminology }} between them. See <a href="docs/state_basics/">Program
   State</a> for more details. In our case, the benefit of this separation is
   that `x_addr` and `y_addr` are guaranteed to be distinct pointers.
   
   Note that `ulongR`, i.e. `unsigned long`, is what `size_t` resolves to on the
   machine on which this tutorial was written. The exact type could differ in
   other contexts.
3. The postcondition, written `\post ...`. In our case, the default
   specification for memory safety merely requires that the two references given
   to `swap` are still valid and separate references. Their contents are
   existentially quantified integers (by `Exists (x0 x1 : Z)`). This
   demonstrates the limits of the automatically generated default specification:
   it does not specify the functional behavior of our program.

While the default specification may look quite weak, proving that `swap`
fulfills it provides a number of guarantees that are not immediately obvious.
* `swap` does not free the references `x` and `y`,
* `swap` does not change the type of the content of `x` and `y`,
* `swap` does not access unitialized memory,
* ...
* and, more generally, that `swap` is *safe* in the sense of "free of undefined behavior".

In the <a href="docs/scaffold/by_hand.md">next chapter of this tutorial</a>, we
provide a more precise specification that also encompasses the functional behavior of `swap`.
