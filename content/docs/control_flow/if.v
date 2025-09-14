(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
  int cond(bool test, int thn, int els) {
    if (test) {
      return thn;
    }
    return els;
  }
}}.

Section with_cpp.
Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
(*@END-HIDE@*)
(*|
In this tutorial, we learn how to verify code with `if`.
For this, we'll use the following function which acts like an `if`.
The specification that we will be proving is written in the comment.

```cpp
int cond(bool test, int thn, int els) {
  if (test) {
    return thn;
  }
  return els;
}
```

We'll be proving the following specification:
|*)
cpp.spec "cond(bool, int, int)" with
 (\arg{test} "test" (Vbool test)
  \arg{thn} "thn" (Vint thn)
  \arg{els} "els" (Vint els)
  \post[Vint (if test then thn else els)] emp).
(*|
We start off the proof in the usual way.
|*)
Goal verify[source] "cond(bool, int, int)".
Proof.
  verify_spec; go.
(*
  _ : PostCond
  _ : thn_addr |-> intR 1$m thn
  _ : els_addr |-> intR 1$m els
  _ : test_addr |-> boolR 1$m test
  --------------------------------------∗
  branch.stmt source
    [region: "els" @ els_addr; "thn" @ thn_addr; "test" @ test_addr; return {?: "int"}]
    test (* << the value being considered *)
    (Sseq [Sreturn (Some (Ecast Cl2r (Evar "thn" "int")))]) (Sseq [])
    (Kseq
       (wp_block source
          [region: "els" @ els_addr; "thn" @ thn_addr; "test" @ test_addr; return {?: "int"}]
          [Sreturn (Some (Ecast Cl2r (Evar "els" "int")))])
       (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v))))
 *)

(*|
At this point, the proof is stuck on the case split which is reflected by `branch.stmt`, i.e. a statement-level branch.

## Manual Verification

The simplest thing that we can do at this point is to use the `wp_if` tactic to tell the automation that we want to consider both cases.
|*)
  wp_if.
  (*
  test = true
  → ...
    --------------------------------------∗
    ::wpS
      [region: "els" @ els_addr; "thn" @ thn_addr; "test" @ test_addr; return {?: "int"}]
      (Sseq [Sreturn (Some (Ecast Cl2r (Evar "thn" "int")))])

goal 2 (ID 1965) is:
  test = false
  → ...
    --------------------------------------∗
    ::wpS
      [region: "els" @ els_addr; "thn" @ thn_addr; "test" @ test_addr; return {?: "int"}] (Sseq [])
    *)
(*|
The first case corresponds to `test = true` and the second case corresponds to `test = false`.
In both of these, the proof can be discharged trivially, and we can achieve this by running `all: go.`
|*)
  all: go.
Qed.
(*|
We can also chain using a `;`, i.e. `wp_if; go.`.
|*)
Goal verify[source] "cond(bool, int, int)".
Proof.
  verify_spec; go.
  wp_if; go.
Qed.

(*|
### Automatic Case Splitting

In cases such as this one, where the two branches of the `if` do not re-join before the end of the function, this sort of case splitting is almost always what we want to do.
To tell the automation to do this automatically, we can use a hint.
|*)
Goal verify[source] "cond(bool, int, int)".
Proof.
  verify_spec; go.
  go using smash_delayed_case_no_join_B.
Qed.
(*|
The `_no_join` part of this is introducing a guard that ensures that at least one side of the `if` statement can not finish "normally".
This avoids the case split when the rest of the code might be difficult, or expensive, to verify.

If we want the automation to always perform the case splits for us, we can use the unguarded hint `smash_delayed_case_B` in a similar way.
|*)
Goal verify[source] "cond(bool, int, int)".
Proof.
  verify_spec; go.
  go using smash_delayed_case_B.
Qed.
(*|
This is especially useful for small functions whose implementation is effectively a single `if`.

## A Note
Splitting the goal directly like this is quite common, but it can be a bit dangerous because it requires that we prove the code after the `if` statement for each branch.
We will discuss specifying "join points" in a subsequent tutorial.
|*)
(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
