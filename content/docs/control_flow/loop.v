(*|
In this tutorial, we learn how to specify a simple loop invariant.
|*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

(*| The AST `source` contains our example C++ loop, which increments
`0` for 10 times. |*)
cpp.prog source prog cpp:{{
  int loop() {
    int i = 0;
    while (i < 10) {
      i++;
    }
    return i;
  }
}}.

(*|
## Specifying and Verifying a Loop

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
`go` will not solve the whole proof on its own.
The first `go` will solve the obligations for allocating and initializing
the local variable `i` (at the location `i_addr` in Rocq).
We need to specify a *{{ "loop invariant" | terminology }}* for the while-loop.
Here, we use the tactic `wp_while`, which takes a function from the region `ρ`
for local variables to a resource predicate.

Our loop invariant is that, each loop interation starts with the full mutable
ownership of the local variable `"i"`
(at the location `_local ρ "i"` which is also `i_addr`)
with some value `i` that is less than or equal to `10`.

The next `go` uses the full ownership of `i` to reads its current value,
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
Note that in this case wealso  have `i <= 10` from the loop invariant
(established by the last loop iteration), so we can
deduce `i = 10` as well as `_local ρ "i" |-> intR 1$m 10`.
This means that `return i` will read `10` from the local variable and
the function returns `10`.

Note that in both branches, `go` can perform the reasoning that we explained
above on its own, because `go` has been taught about basic arithmetic reasoning.
|*)
