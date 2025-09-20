(*
 * Copyright (c) 2025 BlueRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.auto.cpp.prelude.spec.

Require Import bluerock.cpp.demo.linked_list.linked_list_hpp.

(*|
## Representation Predicates for the Node and the List
|*)
NES.Begin linked_list.
Section reps.
  Context `{Σ : cpp_logic} `{MOD: linked_list_hpp.source ⊧ σ}.

  Definition nodeR (q : cQp.t) (data : N) (next : ptr) : Rep :=
    _field "node::_data" |-> uintR q data **
    _field "node::_next" |-> ptrR<"node"> q next **
    structR "node" q.

  Fixpoint nodesR (q : cQp.t) (ls : list N) : Rep :=
    match ls with
    | [] => nullR
    | data :: ls' =>
      ∃ next : ptr, nodeR q data next ** pureR (next |-> nodesR q ls')
    end.

  Definition R (q : cQp.t) (ls : list N) : Rep :=
    ∃ root : ptr,
    _field "linked_list::_root" |-> ptrR<"node"> q root **
    structR "linked_list" q **
    pureR (root |-> nodesR q ls).
End reps.
#[global] Hint Opaque nodeR nodesR R : br_opacity typeclass_instances.

(*|
## Specifying Node
|*)
NES.Begin node.

  cpp.spec "node::node(unsigned int)" from linked_list_hpp.source
      as ctor_null_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \post this |-> nodeR 1$m data nullptr
  ).

  cpp.spec "node::node(unsigned int, node* )" from linked_list_hpp.source
      as ctor_next_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \arg{next} "next" (Vptr next)
    \post this |-> nodeR 1$m data next
  ).

  cpp.spec "node::~node()" from linked_list_hpp.source as dtor_spec with (
    \this this
    \pre{data next} this |-> nodeR 1$m data next
    \post emp
  ).

  cpp.spec "node::get_data()" from linked_list_hpp.source
      as get_data_spec with (
    \this this
    \prepost{q data next} this |-> nodeR q data next
    \post[Vn data] emp
  ).

  cpp.spec "node::set_data(unsigned int)" from linked_list_hpp.source
      as set_data_spec with (
    \this this
    \arg{data} "data" (Vn data)
    \pre{data_old next} this |-> nodeR 1$m data_old next
    \post this |-> nodeR 1$m data next
  ).

NES.End node.

(*|
## Specifying List
|*)
cpp.spec "linked_list::linked_list(node*)" from linked_list_hpp.source
    as ctor_spec with (
  \this this
  \arg{root} "root" (Vptr root)
  \pre{ls : list N} root |-> nodesR 1$m ls
  \post this |-> R 1$m ls
).

(*| The destructor does not handle deallocation of the nodes. |*)
cpp.spec "linked_list::~linked_list()" from linked_list_hpp.source
    as dtor_spec with (
  \this this
  \pre this |-> R 1$m []
  \post emp
).

cpp.spec "linked_list::length() const" from linked_list_hpp.source
    as length_spec with (
  \this this
  \prepost{ls q} this |-> R q ls
  \post[Vint (trim 32 (lengthZ ls))] emp
).


cpp.spec "linked_list::reverse()" from linked_list_hpp.source
    as reverse_spec with (
  \this this
  \pre{ls} this |-> R 1$m ls
  \post this |-> R 1$m (reverse ls)
).


cpp.spec "linked_list::push(node*)" from linked_list_hpp.source
    as push_spec with (
  \this this
  \arg{node} "node" (Vptr node)
  \pre{n} node |-> nodeR 1$m n nullptr
  \pre{ls} this |-> R 1$m ls
  \post this |-> R 1$m (n :: ls)
).

cpp.spec "linked_list::pop()" from linked_list_hpp.source
    as pop_spec with (
  \this this
  \pre{ls n } this |-> R 1$m (n :: ls)
  \post{node}[Vptr node] node |-> nodeR 1$m n nullptr ** this |-> R 1$m ls
).

cpp.spec "linked_list::append(linked_list*)" from linked_list_hpp.source
    as append_spec with (
  \this this
  \arg{that} "l" (Vptr that)
  \pre{ls1} this |-> R 1$m ls1
  \pre{ls2} that |-> R 1$m ls2
  \post this |-> R 1$m (ls1 ++ ls2) ** that |-> R 1$m []
).

Definition sorted (l : list N) : Prop :=
  forall (i j : nat) (x y : N),
    i < j ->
    l !! i = Some x ->
    l !! j = Some y ->
    (x <= y)%N.

Fixpoint merge (l1 l2 : list N) : list N :=
  let fix merge' (l2 : list N) : list N :=
      match l1, l2 with
      | [], _ => l2
      | _, [] => l1
      | x :: l1', y :: l2' =>
        if decide (x <= y)%N
        then x :: merge l1' l2
        else y :: merge' l2'
      end
  in merge' l2.

cpp.spec "linked_list::merge(linked_list*)" from linked_list_hpp.source
    as merge_spec with (
  \this this
  \arg{that} "l" (Vptr that)
  \pre{ls1} this |-> R 1$m ls1
  \pre{ls2} that |-> R 1$m ls2
  \post this |-> R 1$m (merge ls1 ls2) ** that |-> R 1$m []
).
NES.End linked_list.
