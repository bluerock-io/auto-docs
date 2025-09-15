(*
 * Copyright (C) 2023-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.cpp.demo.aggregate01.Point_hpp_spec.

Require bluerock.auto.cpp.hints.fractional.
#[local] Hint Resolve fractional.UNSAFE_read_prim_cancel : br_opacity.

Section with_Σ.
  Context `{Σ: cpp_logic} {σ : genv}.

  (* Alternative learning hints. *)
  (* Only learn value. *)
  Lemma learnable_pointR q1 q2 m1 m2 :
    Learnable (PointR q1 m1) (PointR q2 m2) [m1 = m2].
  Proof. constructor; apply None. Qed.

  (* Also learn fraction. *)
  Lemma UNSAFE_learnable_pointR q1 q2 m1 m2 :
    Learnable (PointR q1 m1) (PointR q2 m2) [m1 = m2; q1 = q2].
  Proof. constructor; apply None. Qed.

  (* We can only use one hint, and we choose [UNSAFE_learnable_pointR] over
  [learnable_pointR] here. *)
  #[local] Hint Resolve UNSAFE_learnable_pointR : br_opacity.

  #[local] Hint Opaque PointR : br_opacity.
  #[local] Hint Extern 1 (PointR _ _ |-- PointR _ _) => reflexivity : br_opacity.

  Lemma ctor_ok : verify[ Point_hpp.module ] ctor_spec.
  Proof. verify_spec; go. Qed.

  Lemma dtor_ok : verify[ Point_hpp.module ] dtor_spec.
  Proof. verify_spec; go. Qed.

  Lemma getX_ok : verify[ Point_hpp.module ] getX_spec.
  Proof. verify_spec'; rewrite /PointR; go. Qed.

  Lemma getY_ok : verify[ Point_hpp.module ] getY_spec.
  Proof. verify_spec'; rewrite /PointR; go. Qed.

  Lemma mdist_ok : verify[ Point_hpp.module ] mdist_spec.
  Proof. verify_spec; go. Qed.

  Definition mdist_link := [LINK] mdist_ok.
  #[local] Hint Resolve mdist_link : br_opacity.
  Definition getX_link := [LINK] getX_ok.
  #[local] Hint Resolve getX_link : br_opacity.
  Definition getY_link := [LINK] getY_ok.
  #[local] Hint Resolve getY_link : br_opacity.
  Definition ctor_link := [LINK] ctor_ok.
  #[local] Hint Resolve ctor_link : br_opacity.
  Definition dtor_link := [LINK] dtor_ok.
  #[local] Hint Resolve dtor_link : br_opacity.

  (* soundness of the specification *)
  Theorem Point_hpp_ok :
      denoteModule Point_hpp.module |-- public_spec.
  Proof. rewrite /public_spec /=; go. Qed.

End with_Σ.
