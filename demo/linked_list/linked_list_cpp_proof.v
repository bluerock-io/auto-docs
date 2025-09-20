(*
 * Copyright (c) 2025 BlueRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.auto.cpp.prelude.proof.

Require Import bluerock.cpp.demo.linked_list.linked_list_hpp_spec.

Require Import bluerock.cpp.demo.linked_list.linked_list_cpp.

#[local] Set Default Proof Using "Type*".

(*|## Proofs of nodes |*)
NES.Begin linked_list.node.proof.
(*| ### Verifying Constructors and Destructor |*)
Section proofs.
  Context `{Σ : cpp_logic} `{MOD: source ⊧ σ}.

  Lemma ctor_null_ok : verify[linked_list_cpp.source] ctor_null_spec.
  Proof. verify_spec. go. rewrite /nodeR. work. Qed.

  Lemma ctor_next_ok : verify[linked_list_cpp.source] ctor_next_spec.
  Proof. verify_spec. go. rewrite /nodeR. work. Qed.

  Lemma dtor_ok : verify[linked_list_cpp.source] dtor_spec.
  Proof. verify_spec. go. rewrite /nodeR. work. Qed.
End proofs.

(*| ### Veryfing Methods |*)
#[only(lazy_unfold)] derive nodeR.
Section proofs.
  Context `{Σ : cpp_logic} `{MOD: linked_list_cpp.source ⊧ σ}.

  Lemma get_data_ok : verify[linked_list_cpp.source] get_data_spec.
  Proof. verify_spec. go. Qed.

  Lemma set_data_ok : verify[linked_list_cpp.source] set_data_spec.
  Proof. verify_spec. go. Qed.
End proofs.
NES.End linked_list.node.proof.

(*|## Proofs of lists |*)
NES.Begin linked_list.proof.

#[only(lazy_unfold)] derive R.

Section proofs.
  Context `{Σ : cpp_logic} `{MOD: linked_list_cpp.source ⊧ σ}.
  Set Default Proof Using "MOD".

(*| ### Verifying Constructor and Destructor |*)
  Lemma ctor_ok : verify[linked_list_cpp.source] ctor_spec.
  Proof. verify_spec. go. Qed.

  Lemma dtor_ok : verify[linked_list_cpp.source] dtor_spec.
  Proof. verify_spec. go. Qed.

  (*| ### Veryfing Methods |*)
  (*| For lazy unfolding of `nodeR` |*)
  #[local] NES.Open linked_list.node.proof.

  Lemma push_ok : verify[linked_list_cpp.source] push_spec.
  Proof. verify_spec. go. Qed.

  Lemma nodeR_null_False q n next :
    nullptr |-> nodeR q n next |-- False.
  Proof. rewrite /nodeR. work. Qed.
  Definition nodeR_null_False_F := [FWD] nodeR_null_False.

  Lemma pop_ok : verify[linked_list_cpp.source] pop_spec.
  Proof.
    verify_spec. go.
    wp_if => NULL_ROOT.
    - (* root non-null *) go.
    - (* root null: impossible because list is non-empty *)
      go using nodeR_null_False_F.
  Qed.

  Lemma length_ok : verify[linked_list_cpp.source] length_spec.
  Proof.
    verify_spec. go.
    (*| Specify a loop invariant |*)
  Abort.

  Lemma reverse_ok : verify[linked_list_cpp.source] reverse_spec.
  Proof.
    verify_spec. go.
    (*| Specify a loop invariant |*)
  Abort.

  Lemma nodesR_null_nil q ls :
    nullptr |-> nodesR q ls |-- [| ls = [] |].
  Proof. destruct ls; [work|]. work using nodeR_null_False_F. Qed.
  Definition nodesR_null_nil_F := [FWD] nodesR_null_nil.

  Lemma append_ok : verify[linked_list_cpp.source] append_spec.
  Proof.
    verify_spec. go.
    wp_if => NULL_ROOT.
    - (* root null *) go using nodesR_null_nil_F.
    - (* root non-null *) go.
      (*| Specify a loop invariant |*)
  Abort.

  Lemma merge_ok : verify[linked_list_cpp.source] merge_spec.
  Proof.
    verify_spec. go.
    (*| Specify a loop invariant |*)
  Abort.
End proofs.
NES.End linked_list.proof.
