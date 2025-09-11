---
title: Using Default Specifications
no_code: true
eleventyNavigation:
    parent: scaffold
    order: 1
---

:::info
    This tutorial builds on the [Getting Started with Scaffold](getting-started.md) tutorial.
:::

`scaffold` is geared towards incremental verification. It allows users to
iteratively increase the scope of the verification project. Running the
interactive command `scaffold verify` presents us with all available
specification/verification targets (or, in our case, one target), e.g.
functions, but also `enum`s and `struct`s.

Run `scaffold verify`, select the `swap` function, and confirm the choice with **Enter**.

```shell
$ scaffold verify
? What would you like to specify?  
>    swap(size_t &, size_t &) @ src/stage1.cpp
  <DONE>
```

`scaffold` now asks us to select **how** we want to specify the function. We
have several options:

1. Writing a specification by hand,
2. Automatically generating a default specification to verify {{ "memory safety" | terminology }}, or
3. Avoid writing a specification directly and instead direct the tools to reason about it by inlining it.

To keep the example simple, we select `Memory safey`, which will generate a simple specification based on the function's type.

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
`scaffold` collects specifications and proofs of functions from `stage1.cpp`, i.e. `swap` in our case.

```shell
$ tree proof/stage1_cpp/
proof/stage1_cpp/
├── pred.v
├── proof
│   └── swap.v
├── proof.v
└── spec.v
```

:::info
`scaffold` is based on document splices so the special comments that look like
```coq
(*BEGIN:"name"*)
(*END*)
```
are the document portions that `scaffold` will modify. Anything outside of these fragements should be preserved; however, it is always best to use version control and run `scaffold` on a pristine repository state.
:::

Two files are of particular interest to us.
1. `proof/stage1_cpp/spec.v` contains the specification that was generated for us. Since we selected the default specification, we see only following line:
   ```coq
   cpp.spec "swap(size_t &, size_t &)" as swap_spec default.
   ```

2. `proof/stage1_cpp/proof/swap.v` contains a simple proof script that is meant to verify the function. The two relevant lines are:
   ```coq
   Lemma swap_ok : verify[source] "swap(size_t &, size_t &)".
   Proof. verify_spec; go. Qed.
   ```

:::info
`scaffold` follows a particular file structure introducing a directory for each source file and dividing the verification in each directory into the following files:
1. `pred.v` contains representation predicates used to model classes. Hints and properties about these predicates should also go in this files.
2. `spec.v` contains function specifications.
3. `proof/function_name.v` contains the proof of `function_name`.
4. `proof.v` bundles the proofs of all of the functions into an easy to `Import` library.

The decomposition of `pred.v` and `spec.v` is critical in instances where headers depend on each other in a cyclic manner. The decompsition of differnet proof files enables parallel builds and makes batch builds more informative.
:::


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
   in more detail in the chapters on [Program State](/docs/state_basics/) and 
   [Primitive Data](/docs/primitive_reps/main). Here, it
   is sufficient to know that these preconditions specify the contents of our
   C++ references, establishing the connection between the C++ state (i.e. the
   memory to which our references point) and our verification variables `x` and
   `y`.
   
   Specifying multiple preconditions establishes a {{ "separating conjunction" |
   terminology }} between them. See [Program State](/docs/state_basics/)
   for more details. In our case, the benefit of this separation is
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

In the [next chapter of this tutorial](docs/scaffold/by_hand.md), we
provide a more precise specification that also encompasses the functional behavior of `swap`.
