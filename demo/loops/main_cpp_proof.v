(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.demo.loops.main_cpp.

Import auto_frac.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : main_cpp.module ⊧ σ}.

  (*| These hints automatically break apart conditionals that would otherwise split
     the goal.

     The `_no_join` variant of `smash_delayed_case` will only split the goal if
     one of the two branches can not terminate normally, e.g. by ending in a
     `<break`, `continue`, `return`, or `throw`.
  |*)
  #[local] Hint Resolve smash_delayed_case_no_join_B : db_bluerock_wp.
  #[local] Hint Resolve vc_split.split_if : br_opacity.

  (*| ## Verification of `while` loops |*)

  cpp.spec "while_loop()" as while_loop with
      (\post[Vint 10] emp).

  Lemma while_loop_ok_inv : verify[main_cpp.module] "while_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
       loop test is evaluated. |*)
    wp_while (fun ρ =>
                Exists x, _local ρ "i" |-> intR 1$m x ** [| 0 <= x < 10 |])%Z.
    (*| running `work` here produces a `wp (Sif ...) ...` for evaluating the condition.
       With the `smash_delayed_case_no_join_B` hint above, `go` will smash this. |*)

    (* TODO: should we avoid the [wp (Sif ..) ..] and immediately go [delayed_case]?
       We could even go farther because we know that one branch of the [delayed_case]
       is just end the loop.
    *)
    go with pick_frac.
  Qed.

  Lemma while_loop_ok_prepost : verify[main_cpp.module] "while_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
       loop test is evaluated. |*)
    wp_while (fun ρ =>
       \pre{x} _local ρ "i" |-> intR 1$m x
       \require (0 <= x < 10)%Z
       \post _local ρ "i" |-> intR 1$m 10).
    (*| running `work` here produces a `wp (Sif ...) ...` for evaluating the condition.
       With the `smash_delayed_case_no_join_B` hint above, `go` will smash this.
    |*)
    go with pick_frac.
  Qed.

  (*| ### `while` loops with declarations |*)
  cpp.spec "while_decl_loop()" as while_decl_loop with
      (\post[Vint 10] emp).

  Lemma while_decl_loop_ok_inv : verify[main_cpp.module] "while_decl_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
       variable is declared.
       This is necessary because the variable is declared at the beginning
       of each iteration of the loop and destroyed at the end.
     |*)
    wp_while (fun ρ =>
                Exists x, _local ρ "i" |-> intR 1$m x ** [| 0 <= x < 10 |])%Z.
    go with pick_frac.
  Qed.

  Lemma while_decl_loop_ok_prepost : verify[main_cpp.module] "while_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
       variable is declared.
       This is necessary because the variable is declared at the beginning
       of each iteration of the loop and destroyed at the end.
    |*)
    wp_while (fun ρ =>
       \pre{x} _local ρ "i" |-> intR 1$m x
       \require (0 <= x < 10)%Z
       \post _local ρ "i" |-> intR 1$m 10).
    go with pick_frac.
  Qed.

  (*| ## Verification of `do-while` loops |*)

  cpp.spec "do_while_loop()" as do_while_loop with
     (\post[Vint 10] emp).

  Lemma do_while_loop_ok_inv : verify[main_cpp.module] "do_while_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
        loop test is evaluated |*)
    wp_do_while (fun ρ =>
      Exists x, _local ρ "i" |-> intR 1$m x ** [| 0 <= x < 10 |])%Z.
    go with pick_frac.
  Qed.


  Lemma do_while_loop_ok_prepost : verify[main_cpp.module] "do_while_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
        loop test is evaluated |*)
    wp_do_while (fun ρ =>
       \pre{x} _local ρ "i" |-> intR 1$m x
       \require (0 <= x < 10)%Z
       \post _local ρ "i" |-> intR 1$m 10).
    (*| running `work` here produces a `wp (Sif ...) ...` for evaluating the condition.
       With the `smash_delayed_case_no_join_B` hint above, `go` will smash this.
    |*)
    go with pick_frac.
  Qed.

  (*| ## Verification of `for` loops |*)

  cpp.spec "for_loop()" as for_loop with
     (\post[Vint 10] emp).

  Lemma for_loop_ok_inv : verify[main_cpp.module] "for_loop()".
  Proof using MOD.
    verify_spec'; go.
    (*| Specify a loop invariant which holds immediately *before* the
        loop test is evaluated |*)
    wp_for (fun ρ =>
              Exists x, _local ρ "i" |-> intR 1$m x ** [| 0 <= x < 10 |])%Z.
    (*| running `work` here produces a `wp (Sif ...) ...` for evaluating the condition.
       With the `smash_delayed_case_no_join_B` hint above, `go` will smash this.
    |*)
    go with pick_frac.
  Qed.

  (*| NOTE: `for_loop` can not be verified using a pre-post specification of
     the loop invariant because the loop body contains a `return`. |*)

End with_cpp.
