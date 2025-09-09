(*|
In this tutorial, we consider specifications and verifications of very simple
programs. These include additions of integers and a swap function.
|*)
(*|
## Simple Functions
Import the C++ verification environment:
|*)
Require Import bluerock.auto.cpp.prelude.proof.

(*| Import the command `cpp.prog` to inline our C++ functions in Rocq. |*)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

(*| Define AST `source` containing our example C++ functions. |*)
cpp.prog source prog cpp:{{
  int add(int x, int y) {
    return x + y;
  }

  unsigned int add(unsigned int x, unsigned int y) {
    return x + y;
  }

  void swap(int* px, int* py) {
    int t = *px;
    *px = *py;
    *py = t;
  }
}}.

(*|
## Specifying and Verifying Integer Addition
We can specify our functions as follows.
|*)

cpp.spec "add(int, int)" from source as add_spec with (
  \arg{x} "x" (Vint x)
  \arg{y} "y" (Vint y)
  (* - 2^31 ≤ x + y ≤ 2^31 - 1 *)
  \require bitsize.bound bitsize.W32 Signed (x + y)
  \post[Vint (x + y)] emp
).

cpp.spec "add(unsigned int, unsigned int)" from source as add_unsigned_spec with (
  \arg{x} "x" (Vint x)
  \arg{y} "y" (Vint y)
  \post[Vint (trim 32 (x + y))] emp
).

(*|
Here, `add_spec` requires strong conditions on the signed arguments `x` and `y`:
the sum of `x` and `y` should neither underflow nor overflow for 32-bit integers.
That is, `x + y` should be in the range `[-2^31,2^31)`. As such, the function
will return the sum as-is.
`\require P` adds a pure Rocq proposition (`P : Prop`) as a pre-condition to
the specification.

On the other hand, `add_unsigned_spec` does not require any condition on the
unsigned integers `x` and `y`. Instead, it returns, in the post-condition, the
sum of `x` and `y` potentially truncated to 32 bits (`trim 32 (x + y)`),
covering the case where the sum overflows.
In case that we know that the sum does not overflow, i.e., `x + y < 2^32`, we can
use `modulo.useless_trim` to get the equality `trim 32 (x + y) = x + y`.
|*)
About modulo.useless_trim.
(*
modulo.useless_trim :
∀ (a : Z) (bits : N), (0 ≤ a < 2 ^ bits)%Z → a = trim bits a
*)
(*| (Note that as `x` and `y` are unsigned, we do have `0 ≤ x + y`.) |*)


Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : !source ⊧ σ}.

  Lemma add_spec_ok : verify[source] "add(int, int)".
  Proof.
    verify_spec. go.
  Qed.

  Lemma add_unsigned_spec_ok : verify[source] add_unsigned_spec.
  Proof. verify_spec. go. Qed.
End with_cpp.

(*|
With the correct specifications and the fact that the code is very simple,
the `go` tactics of the the BlueRock's automation can discharged the proofs
without extra intervention.
One can try to change the specifications, for example by removing the required
resources or the `bitsize.bound` pre-condition, to see that the automation may
fail to finish the proofs.

Note that we can use the `verify[source]` notation with either the C++ function
name or the Rocq specification name. In case of the former, the notation will
look up in the environment to find the corresponding Rocq specification, e.g.,
`verify[source]` will find that `add_spec` is the specification for `add(int,int)`
and generate the expected lemma statement.
|*)

(*|
## Specifying and Verifying Swap
|*)

cpp.spec "swap(int*, int* )" from source as swap_spec with (
  \arg{px} "px" (Vptr px)
  \arg{py} "py" (Vptr py)
  \pre{x} px |-> intR 1$m x
  \pre{y} py |-> intR 1$m y
  \post px |-> intR 1$m y ** py |-> intR 1$m x
).

(*|
The specification for `swap` requires in the pre-condition the full, *mutable*
ownership (with fraction `1$m`) of both locations `px` and `py`,
with some intial values `x` and `y`, respectively.
The result, as stated in the post-condition, is that the values `x` and `y`
are swapped.
|*)
Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : !source ⊧ σ}.

  Lemma swap_ok : verify[source] swap_spec.
  Proof. verify_spec. go. Qed.
End with_cpp.

(*| Again, the automation can solve this goal on its own.
If, however, we have a specification with insufficient pre-conditions, such as
`not_enough_resources_swap_spec` below, where we do not have full, mutable
ownership of `px` and `py`
(`(1/2)$c` means we only have half the fraction, with only read permission),
then the automation will fail to finish the proof.
|*)
cpp.spec "swap(int*, int* )" from source as not_enough_resources_swap_spec with (
  \arg{px} "px" (Vptr px)
  \arg{py} "py" (Vptr py)
  \pre{x} px |-> intR (1/2)$c x
  \pre{y} py |-> intR 1$m y
  \post px |-> intR 1$m y ** py |-> intR 1$m x
).

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : !source ⊧ σ}.

  Example not_enough_resources_swap_not_ok : verify[source] not_enough_resources_swap_spec.
  Proof. verify_spec. go. Fail Qed. Abort.
End with_cpp.
