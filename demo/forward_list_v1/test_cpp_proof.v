(*
 * Copyright (c) 2025 BlueRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*|
This demonstrates a _simple_ way of specifying `forward_list` and its iterators.
Rather than precisely tracking the index that the iterator is in, we instead
simply track whether the iterator references an actual node or a past-the-end node.
This ensures memory safety.

The specifications of the standard library will support functional correctness reasoning.
|*)
Require Import bluerock.auto.cpp.prelude.spec.
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.cpp.demo.forward_list_v1.test_cpp.

Implicit Type (p : ptr).

(* BEGIN: Upstream *)
Section with_Σ.
  Context `{Σ : cpp_logic}.
  Definition wand_p_CX {A : Type} p (Q : A -> Rep) := wand.wand_CX (λ y, p |-> Q y).
End with_Σ.
Create HintDb wand_db discriminated.
#[local] Hint Resolve wand_p_CX : wand_db.

Ltac merge_wand := wname [bi_wand] "W"; iDestruct ("W" with "[$]") as "?".
Ltac admit_spec spec := iAssert spec as "#?"; first admit.
(* END: Upstream *)

NES.Begin std.forward_list.

  Notation N := "std::__1::forward_list<int, std::__1::allocator<int>>"%cpp_name.
  Notation T := "std::__1::forward_list<int, std::__1::allocator<int>>"%cpp_type.
  Goal T = Tnamed N. done. Abort.

  (* The name of the iterator type. *)
  Notation itN := "std::__1::__forward_list_iterator<std::__1::__forward_list_node<int, void*>*>"%cpp_name.

  (*| Representation predicate for `forward_list<int>`. |*)
  br.lock Definition R `{Σ : cpp_logic, σ : genv} (q : cQp.t) (xs : list Z): Rep :=
    structR N q.
  #[only(type_ptr,cfracsplittable)] derive R.
  (** [b] is true for non-past-the-end iterators. *)

  (*| Representation predicate for `forward_list<int>::iterator`.

      `own` is a snapshot of the list model at the time that the iterator was created.
     `b = true` means that this iterator is not at the end.
  |*)
  br.lock Definition itR `{Σ : cpp_logic, σ : genv}
      (own : option (ptr * cQp.t * list Z)) q (b : bool): Rep :=
    structR itN q.
  #[only(type_ptr,cfracsplittable)] derive itR.

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv}.
    Context `{MOD : test_cpp.source ⊧ σ}.

    #[global] Instance R_learn
      : Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) R) := ltac:(solve_learnable).

    #[global] Instance itR_learn
      : Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) itR) := ltac:(solve_learnable).

    cpp.spec "std::forward_list<int, std::allocator<int>>::forward_list()"
        as ctor_spec with
     (\this this
      \post this |-> R 1$m []).

    cpp.spec "std::forward_list<int, std::allocator<int>>::~forward_list()"
      as dtor_spec with
     (\this this
      \pre{xs} this |-> R 1$m xs
      \post emp).

    cpp.spec "std::forward_list<int, std::allocator<int>>::push_front(int&&)"
      as push_front_move_spec with
     (\this this
      \pre{ns} this |-> R 1$m ns
      \arg{p} "n" (Vref p)
      \prepost{q n} p |-> intR q n
      \post this |-> R 1$m (n :: ns)).

    cpp.spec "std::forward_list<int, std::allocator<int>>::pop_front()"
      as pop_front_move_spec with
     (\this this
      \pre{n ns} this |-> R 1$m (n :: ns)
      \post this |-> R 1$m ns).

    cpp.spec "std::forward_list<int, std::allocator<int>>::empty() const"
      as empty_spec with
     (\this this
      \prepost{ns} this |-> R 1$m ns
      \post[Vbool (bool_decide (ns = []))] emp).

    (*| This specification consumes the entire list in order to check out a single
       value. This is similar to Rust's handling of array access, once you perform
       a mutable borrow of an element from an array, you can not borrow more elements.

       Stronger specifications exist, but they require finer-grained tracking
       of the values.
    |*)
    cpp.spec "std::forward_list<int, std::allocator<int>>::front()"
      as front_spec with
      (\this this
      \pre{n ns} this |-> R 1 (n :: ns)
      \post{p}[Vref p]
        p |-> intR 1$m n **
        (p |-> intR 1$m n -* this |-> R 1 (n :: ns))).

    (*| ## Iterators

        Creating an iterator consumes part of the underlying list.
        This is necessary to prevent concurrent modifications to the list.
    |*)
    cpp.spec "std::forward_list<int, std::allocator<int>>::begin()"
        as begin_spec with (
      \this this
      \pre{q ns} this |-> R q ns
      \post{p}[Vptr p] p |-> itR (Some (this, q, ns)) 1$m (bool_decide (ns <> nil))
      (* ^^ Return a past-the-end iterator for empty lists. *)
    ).

    cpp.spec "std::forward_list<int, std::allocator<int>>::end()"
        as end_spec with (
      \this this
      \pre{q ns} this |-> R q ns
      \post{p}[Vptr p] p |-> itR (Some (this, q, ns)) 1$m false
    ).

    cpp.spec "std::operator==(const std::__forward_list_iterator<std::__forward_list_node<int, void*>*>&, const std::__forward_list_iterator<std::__forward_list_node<int, void*>*>&)"
      as it_eq_spec with (
          \arg{r1} "" (Vref r1)
            \arg{r2} "" (Vref r2)
            \prepost{m1 q1 b1} r1 |-> itR m1 q1 b1
            \prepost{m2 q2 b2} r2 |-> itR m2 q2 b2
            \post{b}[Vbool b] [| if b then b1 = b2
                                 else b1 = true \/ b2 = true |]
        ).

    cpp.spec "std::operator!=(const std::__forward_list_iterator<std::__forward_list_node<int, void*>*>&, const std::__forward_list_iterator<std::__forward_list_node<int, void*>*>&)"
        as it_ne_spec with (
      \arg{r1} "" (Vref r1)
      \arg{r2} "" (Vref r2)
      \prepost{m1 q1 b1} r1 |-> itR m1 q1 b1
      \prepost{m2 q2 b2} r2 |-> itR m2 q2 b2
      \post{b}[Vbool b] [| if bool_decide (b = false) then b1 = b2
                           else b1 = true \/ b2 = true |]
    ).

    cpp.spec "std::__forward_list_iterator<std::__forward_list_node<int, void*>*>::~__forward_list_iterator()"
        as it_dtor_spec with (
      \this this
      \pre{m b} this |-> itR m 1$m b
      \post match m with
            | None => emp
            | Some (p, q, ls) => p |-> R q ls
            end
    ).

    cpp.spec "std::__forward_list_iterator<std::__forward_list_node<int, void*>*>::operator++()"
      as it_op_pre_plusplus
      with (
        \this this
        \pre{m} this |-> itR m 1$m true
        \post{b'}[Vptr this] this |-> itR m 1$m b'
    ).

    (*| Similar to `front` above, this specification consumes the entire iterator
       ownership in order to check out the current value.
       See the comment there for more information.
    |*)
    cpp.spec "std::__forward_list_iterator<std::__forward_list_node<int, void*>*>::operator*() const"
        as it_op_star_spec with (
      \this this
      \let{lp q ls} m := Some (lp, q, ls)
      \pre this |-> itR m 1$m true
      \post{p}[Vptr p] ∃ i,
        p |-> intR q i **
        (p |-> intR q i -* this |-> itR m 1$m true)
      (* TODO AUTO: this type error produces a raw [False] *)
    ).

  End with_Σ.

NES.End std.forward_list.

Section with_Σ.
  Context `{Σ : cpp_logic, σ : genv}.

  NES.Open std.forward_list.

  Section with_MOD.
    Context `{MOD : test_cpp.source ⊧ σ}.

    cpp.spec "test(bool)" as test_spec with (
      \arg "b" (Vbool true)
      \post emp
    ).

    (* TODO: aliases do not work under <<template>> because we do not have access to the
       template AST. *)
    cpp.spec "TestBasic<template std::__1::forward_list>()" as test_basic with (
      \post emp
    ).

    cpp.spec "main()" as main with (
      \post[Vint 0] emp
    ).

    cpp.spec "TestIterators<template std::__1::forward_list>()" as test_iterators with (
      \post{n}[Vint n] emp).

  End with_MOD.

  Section iterators.

    Lemma test_iterators_ok : verify[source] test_iterators.
    Proof.
      verify_spec. go.
      progress name_locals.

      wp_for (fun ρ =>
          \pre{b} __begin0_addr |-> itR ?[m] 1$m b
          \pre{n} acc_addr |-> uintR 1$m n
          \post* ∃ n', acc_addr |-> uintR 1$m n'
          \post Exists b', __begin0_addr |-> itR ?m 1$m b').
      go.
      wp_if; first last. { go. }
      go.
      simplify_eq/=.
      destruct_or!; try by exfalso.
      ego.
    Qed.

  End iterators.

  Section basic.
    Lemma test_basic_ok : verify[source] test_basic.
    Proof.
      verify_spec. go.
      go with #wand_db.
    Qed.
  End basic.
End with_Σ.
