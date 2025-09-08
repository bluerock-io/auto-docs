(*|
In this tutorial, we consider specifications and verifications of verify simple
programs. These include additions of integers, a swap function, and
a function that loops 10 times.
|*)
(*|
# Simple Functions
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

  int loop() {
    int i = 0;
    while (i < 10) {
      i++;
    }
    return i;
  }
}}.

(*|
# Specifying and Verifying Integer Addition
We can specify our functions as follows.
|*)

cpp.spec "add(int,int)" from source as add_spec with (
  \arg{x} "x" (Vint x)
  \arg{y} "y" (Vint y)
  (* - 2^31 ≤ x + y ≤ 2^31 - 1 *)
  \require bitsize.bound bitsize.W32 Signed (x + y)
  \post[Vint (x + y)] emp
).

cpp.spec "add(unsigned int,unsigned int)" from source as add_unsigned_spec with (
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

  Lemma add_spec_ok : verify[source] "add(int,int)".
  Proof.
    (* denoteModule source ⊢ add_spec *)
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
# Specifying and Verifying Swap
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

(*|
# Specifying and Verifying a Loop

The specification is indeed very simple: the function returns `10`, the result of
incrementing `0` 10 times.
|*)

cpp.spec "loop()" from source as loop_spec with (
  \post[Vint 10] emp
).

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : !source ⊧ σ}.

  Lemma loop_ok : verify[source] "loop()".
  Proof using MOD.
    verify_spec. go.
    (* specifying a loop invariant *)
    wp_while (fun ρ => ∃ i, _local ρ "i" |-> intR 1$m i ** [| (i <= 10)%Z |])%I.
    go.
    wp_if => Lt10.
    - (* Less than 10, increment *) go.
    - (* Not less than 10, break *) go.
  Qed.
End with_cpp.

(*|
`go` will not solve the goal on its own.
We need to specify a *{{ "loop invariant" | terminology }}* for the while-loop.
Here, we use the tactic `wp_while`, which takes a function from the region `ρ`
for local variables to a resource predicate.
Our loop invariant is that, each loop interation starts with the full mutable
ownership of the local variable `"i"` with some value `i` that is less than
or equal to `10`.

The next `go` use the full ownership of `i` to reads its current value,
and leaves us with the goal of the loop's conditional `(i < 10)`.
Here, we use the `wp_if` tactic to make the case distinction.
- If the conditional holds, we enter the loop iteration, and we have
the full mutable permission of `"i"` to increment it by `1`.
That is, the loop body turns `_local ρ "i" |-> intR 1$m i` into 
`_local ρ "i" |-> intR 1$m i + 1`.
Note that if this is the last loop iteration, we will then have `i + 1 = 10`,
which is still sufficient to re-establish the loop invariant with `i + 1 <= 10`.
- If the conditional does not hold, we have `_local ρ "i" |-> intR 1$m i` and
`¬ i < 10` and the loop terminates.
Note that in which case we have `i <= 10` from the loop invariant, so we can
deduce `i = 10` as well as `_local ρ "i" |-> intR 1$m 10`.
This means that `return i` will read `10` from the local variable and returns `10`.

Note that in both branches,  `go` can perform the reasoning that we explained above
on its own.
|*)
