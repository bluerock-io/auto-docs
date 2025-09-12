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
specification/verification targets (or, in our case, one target).

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
2. Automatically generating a default, memory safety, specification, or
3. Direct the tools to reason about it by inlining it.

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

The `proof/` directory now contains a new directory called `stage1_cpp`.
In it, `scaffold` collects specifications and proofs of functions from `stage1.cpp`, i.e. `swap`.

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
are the document portions that `scaffold` will modify. Anything outside of these fragements should be preserved; however, it is always best to use version control and to run `scaffold` on a pristine repository state.
:::

Two files are of particular interest to us.
1. `proof/stage1_cpp/spec.v` contains the specification that `scaffold` generated for us.
   Since we selected the default specification, we see only following line:
   ```coq
   cpp.spec "swap(size_t &, size_t &)" as swap_spec default.
   ```

2. `proof/stage1_cpp/proof/swap.v` contains a simple proof script that is meant to verify the function.
   The two relevant lines are:
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

The decomposition of `pred.v` and `spec.v` is critical in instances where headers depend on each other in a cyclic manner. The decompsition of different proof files enables parallel builds and makes batch builds more informative.
:::


Even though the proof ends with `Qed`, it has not actually been checked yet. We
can run `dune build proof/` (or `dune b proof/` for short) to check the proof is
indeed correct. The command should succeed.

```shell
$ dune b proof/
```

## What Have We Proven?

To check the specification that `scaffold` generated for `swap`, open the file `proof/stage1_cpp/spec.v` and add `Print swap_spec.` to the end of the file.
To see the result, we can run `dune` again.

```shell
$ dune b proof/
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

:::info
Rocq also allows us to evaluate the file in an editor and interact with it directly.
This is an important feature that we will see [in the next section](by_hand.md).
:::

In `scaffold` ,the default specification for a function is formed by specifying the basic ownership of each type with existentially quantified values.
For more information on what this specification means, check out [the documentation on function specifications](/docs/specifications.v).

While the default specification doesn't say that the function actually swaps its arguments, the proof of it does guarantee the absence of [undefined behavior]() as long as the pre-condition holds when calling the function.
This includes properties such as
* `swap` does not free the references `x` and `y`,
* `swap` does not change the type of the content of `x` and `y`,
* `swap` does not access unitialized memory,
* ... and more ...

## Up Next

In the [next chapter of this tutorial](docs/scaffold/by_hand.md), we
provide a more precise specification that also encompasses the functional behavior of `swap`.
