(*@HIDE@*)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
Require Import bluerock.auto.cpp.prelude.spec.

cpp.prog source prog cpp:{{
  const int foo = 3;

  void test() {}

  void int_arg(int x);

  int int_return();

  void ref_arg(int& r);

  void rv_ref_arg(int&& r);
}}.

#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
(*@END-HIDE@*)
(*|

This file is based on the following code.

```cpp
const int foo = 3;

void test() {}

void int_arg(int x);

int int_return();

void ref_arg(int& r);

void rv_ref_arg(int&& r);
```


Function-level specifications are at the heart of modular verification.
In BRiCk, function specifications are written in a syntax inspired by [Doxygen](https://www.doxygen.nl/) using `\` commands.

## The Post-condition - `\post`

All function specifications must end with a `\post` line.
If the function returns `void`, then the syntax is the following:
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "test()" with
  (\post emp (* ownership to return *)).
(*|

## Returning Values - `\post[]`

Functions that return values use a special form of `\post` where the return value is placed in `[]`.
For example, if the function `int_return()` always returned the value `0`, then the specification could be written.
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "int_return()" with
  (\post[Vint 0] emp).
(*|

If existential quantifiers are necessary to describe the return value, then these can be added using `{}`.
For example, if we want to say that `int_return()` returns an arbitrary integer, then we could write the following:
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "int_return()" with
  (\post{v}[Vint v] emp).
(*|
Multiple quantifiers are supported as well as quantifiers with type annotations.
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "int_return()" with
  (\post{(v : Z) (w : Z)}[Vint (v + w)] emp).

(*|
## Spatial Pre-conditions - `\pre`

Spatial ownership can be added to the pre-condition of the function using `\pre`.
For example,
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "test()" with
  (\pre _global "foo" |-> intR 1$c 3
   \post emp).
(*|
This specification states that the function `test()` must be called with full (constant) ownership of the global variable `foo` which must have value `3`.
`\pre` supports adding implicit existential quantifiers for logical variables using `{}` notation.
For example,
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "test()" with
  (\pre{x : Z} _global "foo" |-> intR 1$c x
   \post emp).

(*|
## Pure Pre-conditions - `\require`

Non-spatial facts, e.g. `x < 5`, can be added to the pre-condition using `\require`.
As with `\pre`, this supports implicit existentials.
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "test()" with
  (\require{x : Z} x < 5
   \post emp).

(*|
## Primitive Arguments - `\arg`

Arguments of primitive types, e.g. `int`, `char`, `C*`, etc, are described using the `\arg` command, which takes a string name for documentation purposes and a value that the argument must match.
For example, to state that the argument to `int_arg(int)` must be less than `3`, you could write the following:
|*)
(*@HIDE@*)Succeed(*@END-HIDE@*)
cpp.spec "int_arg(int)" with
  (\arg{x : Z} "x" (Vint x)
   \require x < 3
   \post emp).
(*|
As with the other commands, the `{}`s introduce existential quantifiers.
By convention, the name in the string should match the name of the formal, but this is not currently required.

:::info
`cpp.spec` is implicitly adding the pre- and post- ownership for the argument to this specification and can do this because primitives of this form are guaranteed to have trivial destructors.
:::

|*)
(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
