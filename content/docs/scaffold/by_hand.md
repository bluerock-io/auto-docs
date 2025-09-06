---
title: Providing a Specification by Hand
no_code: true
---

In the [previous chapter](docs/scaffold/simple.md), we asked
`scaffold` to generate a default specification in order to prove memory safety
of a simple `swap` function. This tutorial builds upon the previous chapter by
demonstrating how to manually provide a specification for `swap` that fully
specifies the functions behavior. We assumes that the `example/` has been
initialized with `scaffold init` and that all the files of the previous chapter
are still present.

We start by creating a copy of the `swap` function in a new `cpp` file
`src/stage2.cpp`. The code is unchanged from the previous chapter:

```cpp
#include <cstddef>

void swap(size_t& x, size_t& y) {
    size_t tmp = y;
    y = x;
    x = tmp;
}
```

To make sure scaffold understands the new file, we re-run our `bear` and `clang` combination command and add the newly created file.

```shell
$ bear -- clang -c src/stage1.cpp -c src/stage2.cpp
```

Now that `scaffold` understands how to build `stage2.cpp`, we proceed by running
`scaffold verify`. We are presented with two `swap` functions with identical
signatures. Helpfully, `scaffold` indicates which file each of them comes from. We select
the one from `stage2.cpp`, then choose `By hand`, and press **e** to open an
editor. `scaffold` pre-populates the temporary file with specifiers for the
function arguments but leaves the rest to us. (`\post emp` indicates an trivial
postcondition.)

```coq
\arg{x} "x" (Vref x)
\arg{y} "y" (Vref y)
\post emp
```

Building on the default specification that we inspected at the end of the
previous chapter, we want to extend `scaffold`'s bare-bones specification to
properly specify a) the two function arguments of `swap` and their contents, as
well as b) `swap`'s precise postcondition, i.e. the fact it swaps the contents
of its arguments. We thus change the provided specification to:

```coq
\arg{x_addr} "x" (Vptr x_addr)
\pre{x} x_addr |-> ulongR 1$m x 
\arg{y_addr} "y" (Vptr y_addr)
\pre{y} y_addr |-> ulongR 1$m y 
\post 
  x_addr |-> ulongR 1$m y **
  y_addr |-> ulongR 1$m x
```

Compared to the default specification from the previous chapter, we have made
one important change as well as several small cosmetic changes to make the
specification more idiomatic and easier to read.
1. Most importantly, we have removed the existential quantifiers from the
   postcondition. Instead of merely requiring the references to contain any two
   numbers, we now specify exactly that the reference `x` must contain the
   initial value of `y` and vice versa.
2. To make the specification a bit more readable, we omit the types of our
   verification variables. The syntax `\arg{x_addr}` is shorthand for
   `\arg{(x_addr : _)}` which indicates to Rocq that it should infer the type
   from the variable's usage.
4. We introduce the verification variables for the references' contents (`x` and
   `y`) only where we first need them. Similarly to `\arg{..}`, the syntax
   `\pre{..}` generalizes the remaining specification over the variable(s)
   introduced between the curly braces.


We finish the process of manually providing this specification by saving the
file and closing the editor, which brings us back to our interactive `scaffold`
session. As before, select `<DONE>` to write the changes to disk. Finally, run
`scaffold gen` to generate the necessary build system infrastructure that will
allows us to build the generated Rocq files.

```shell
$ scaffold gen
```

This is all we need to have Rocq check this more precise specification. Given
the simplicity of `swap`'s code, BlueRock's proof automation makes short work of
proving the function's correctness against the new specification.

```shell
$ dune b proof/stage2_cpp/
```

Having successfully checked our proof, we can now be certain that `swap` does
indeed swap the contents of its two arguments.
