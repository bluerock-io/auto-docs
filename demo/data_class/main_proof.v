(*
 * Copyright (C) BlueRock Security Inc 2025
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.demo.data_class.main_cpp.

(*| In many cases, our `class`es (especially `struct`) contain no real
   abstraction. Rather, they just bundle up some data.

   These "data classes" can be specified automatically using
   `cpp.class`.
|*)

Import wp_path.WpPrimRSep.
Import auto_frac.

Module two_ints.
  cpp.class "two_ints"
    prefix ""
    from main_cpp.source
    dataclass
    { copyable
    ; movable
    ; defaultable }.
End two_ints.

(*| Using the generated [Rep] predicate, specifications, and proofs,
   we can easily verify clients.
|*)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[local] Open Scope Z_scope.

  cpp.spec "add(const two_ints&, const two_ints&)" as add_spec from (main_cpp.source)
    with
    (\arg{ap} "a" (Vref ap)
    \arg{bp} "b" (Vref bp)
    \prepost{qa a} ap |-> two_ints.R qa a
    \prepost{qb b} bp |-> two_ints.R qb b
    \let x2 := a.(two_ints.x) + b.(two_ints.x)
    \let y2 := a.(two_ints.y) + b.(two_ints.y)
    \require valid<"int"> (Vint x2)
    \require valid<"int"> (Vint y2)
    \post{r}[Vref r]
      r |-> two_ints.R 1$m {| two_ints.x := x2 ; two_ints.y := y2 |}).

  Lemma add_ok : verify[main_cpp.source] add_spec.
  Proof.
    verify_spec; go with pick_frac.
  Qed.

  cpp.spec "test()" as test_spec from (main_cpp.source) with
    (\post emp).

  Lemma test_ok : verify[main_cpp.source] test_spec.
  Proof.
    verify_spec; go with pick_frac.
  Qed.
End with_cpp.
