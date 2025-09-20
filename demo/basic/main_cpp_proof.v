(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)


(*|
## Overview
This file contains a number of specifications for simple
functions on primitive C++ types.

The file [main.cpp](main.cpp) has several other functions that
you can try to specify and verify.
|*)

(*| Import the C++ verification environment |*)
Require Import bluerock.auto.cpp.proof.
(*| Import the code that we are going to be verifying |*)
Require Import bluerock.cpp.demo.basic.main_cpp.

(*| ## Automation setup

There are no interesting fractional splitting patterns in this
file, so we enable some aggressive automation heuristics.
|*)
Import auto_frac auto_pick_frac.
Import wp_path.WpPrimRSep.
(*| Automatically split control flow paths when branches do not
    have join points, e.g. if at least one branch contains
    `return`, `break`, or `continue`.
|*)
#[local] Hint Resolve smash_delayed_case_B : br_opacity.

(*| ## Specifications |*)

(** interpret arithmetic operations and integer literals as [Z]. *)
#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "add(int, int)" as add_spec with
     (\arg{x} "x" (Vint x)
      \arg{y} "y" (Vint y)
      \require valid<"int"> (x + y)
      \post[Vint (x + y)] emp).

  Lemma add_ok : verify[main_cpp.source] add_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "doubled(int)" as doubled_spec with
      (\arg{n} "n" (Vint n)
       \require valid<"int"> (2 * n)
       \post[Vint (2 * n)] emp).

  Lemma doubled_ok : verify[main_cpp.source] doubled_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "quadruple(int)" as quadruple_spec with
      (\arg{n} "n" (Vint n)
       \require valid<"int"> (4 * n)
       \post[Vint (4 * n)] emp).

  Lemma quadruple_ok : verify[main_cpp.source] quadruple_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "abs(int)" as abs_spec with
      (\arg{n} "n" (Vint n)
       \require valid<"int"> (Z.abs n)
       \post[Vint $ Z.abs n] emp).


  Lemma abs_ok : verify[main_cpp.source] abs_spec.
  Proof. verify_spec; go. Qed.

  (*| ### Pointers and Simple Ownership |*)

  cpp.spec "read(int*)" as read_spec with
      (\arg{p} "p" (Vptr p)
       \prepost{q v} p |-> intR q v
       \post[Vint v] emp).

  Lemma read_ok : verify[main_cpp.source] read_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "quadruple_mem(int*)" as quadruple_mem_spec with
     (\arg{p} "p" (Vptr p)
      \prepost{q v} p |-> intR q v
      \require valid<"int"> (4 * v)
      \post[Vint $ 4 * v] emp).

  Lemma quadruple_mem_ok : verify[main_cpp.source] quadruple_mem_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "abs_mem(int*)" as abs_mem_spec with
     (\arg{p} "p" (Vptr p)
      \prepost{q v} p |-> intR q v
      \require valid<"int"> (Z.abs v)
      \post[Vint $ Z.abs v] emp).

  Lemma abs_mem_ok : verify[main_cpp.source] abs_mem_spec.
  Proof. verify_spec; go. Qed.

  (*| ### Writing to Memory |*)

  cpp.spec "incr(int*)" as incr_spec with
      (\arg{p} "p" (Vptr p)
       \pre{v} p |-> intR 1$m v
       \require valid<"int"> (v + 1)
       \post p |-> intR 1$m (1 + v)).

  Lemma incr_ok : verify[main_cpp.source] incr_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "zero(int*)" as zero_spec with
      (\arg{p} "p" (Vptr p)
       \pre p |-> anyR Tint 1$m
       \post p |-> intR 1$m 0).

  Lemma zero_ok : verify[main_cpp.source] zero_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "inplace_double(int*)" as inplace_double_spec with
      (\arg{p} "p" (Vptr p)
       \pre{v} p |-> intR 1$m v
       \require valid<"int"> (2 * v)
       \post p |-> intR 1$m (2 * v)).

  Lemma inplace_double_ok : verify[main_cpp.source] inplace_double_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "add_mem(unsigned int*, unsigned int*)" as add_mem_spec with (
    \arg{p} "p" (Vptr p)
    \arg{q} "q" (Vptr q)
    \prepost{m qm} p |-> uintR qm$c m
    \prepost{n qn} q |-> uintR qn$c n
    \require valid<"unsigned"> (m + n)
    \post[Vint (m + n)] emp
  ).

  Lemma add_mem_ok : verify[main_cpp.source] add_mem_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "swap(unsigned int*, unsigned int*)" as swap_spec with (
    \arg{p} "p" (Vptr p)
    \arg{q} "q" (Vptr q)
    \pre{m} p |-> uintR 1$m m
    \pre{n} q |-> uintR 1$m n
    \post p |-> uintR 1$m n ** q |-> uintR 1$m m
  ).

  Lemma swap_ok : verify[main_cpp.source] swap_spec.
  Proof. verify_spec; go. Qed.
End with_cpp.

(*| ### Aggregates |*)

Module manually.
  (*| A simple `Rep`resentation predicate (aka class invariant) for
   `struct point`. |*)
  br.lock
  Definition pointR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (m : Z * Z) :=
    structR "point" q **
    _field "point::x" |-> intR q (fst m) **
    _field "point::y" |-> intR q (snd m).
  #[only(lazy_unfold)] derive pointR. (* boiler-plate to derive some hints for field access *)

  Section with_cpp.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

    cpp.spec "transpose(point*)" as transpose_spec with
        (\arg{p} "p" (Vptr p)
         \pre{m} p |-> pointR 1$m m
         \post p |-> pointR 1$m (m.2, m.1)).

    Lemma transpose_ok : verify[main_cpp.source] transpose_spec.
    Proof using MOD. verify_spec; go. Qed.
  End with_cpp.
End manually.

Module data_classes.
  Module point.
    cpp.class "point" prefix "" from source dataclass.
  End point.

  Section with_cpp.
    Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

    cpp.spec "transpose(point*)" as transpose_spec with
        (\arg{p} "p" (Vptr p)
         \pre{m} p |-> point.R 1$m m
         \post p |-> point.R 1$m
         {| point.x := m.(point.y) ; point.y := m.(point.x) |}).

    Lemma transpose_ok : verify[main_cpp.source] transpose_spec.
    Proof using MOD. verify_spec; go. Qed.
  End with_cpp.
End data_classes.
