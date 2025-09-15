(*
 * Copyright (C) 2019-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.auto.cpp.specs.
Require Import bluerock.cpp.demo.aggregate01.Point_hpp.

#[local] Open Scope Z_scope.

Record Model_Point : Type :=
  { point_x : Z
  ; point_y : Z
  }.

Section with_Σ.
  Context `{Σ:cpp_logic} `{Point_hpp.module ⊧ σ}.

  Definition PointR (q : cQp.t) (m : Model_Point) : Rep :=
    _field "Point::x" |-> intR q m.(point_x) **
    _field "Point::y" |-> intR q m.(point_y) **
    structR "Point" q.
  #[global] Hint Opaque PointR : typeclass_instances br_opacity.
  #[only(type_ptr,cfractional)] derive PointR.

  #[global] Instance : forall q m, Observe (type_ptrR _) (PointR q m) := _.

  cpp.spec "Point::Point(int, int)" as ctor_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \arg{y} "y" (Vint y)
     \post this |-> PointR 1$m {| point_x := x; point_y := y |}
    ).

  cpp.spec "Point::~Point()" as dtor_spec with
    (\this this
     \pre  Exists m, this |-> PointR 1$m m
     \post emp
    ).

  cpp.spec "Point::getX() const" as getX_spec with
    (\this this
     \prepost{q m} this |-> PointR q m
     \post[Vint m.(point_x)] emp
    ).

  cpp.spec "Point::getY() const" as getY_spec with
    (\this this
     \prepost{m q} this |-> PointR q m
     \post[Vint m.(point_y)] emp
    ).

  (*| The side conditions `valid<"int"> v` assert that the value
     `v` must be a valid value of type `int`. These are required
     because signed integer overflow is undefined behavior in C++.
  |*)
  cpp.spec "Point::mdist(const Point&) const" as mdist_spec with
    (\this this
     \arg{other} "other" (Vptr other)
     \prepost{q1 m1} this |-> PointR q1 m1
     \prepost{q2 m2} other |-> PointR q2 m2
     \let dx := m2.(point_x) - m1.(point_x)
     \let dy := m2.(point_y) - m1.(point_y)
     \require valid<"int"> dx
     \require valid<"int"> dy
     \require valid<"int"> (dx + dy)
     \post[Vint (dx + dy)] emp
    ).

  Definition public_spec : mpred :=
    ctor_spec ** dtor_spec ** getX_spec ** getY_spec ** mdist_spec.

End with_Σ.
#[only(lazy_unfold)] derive PointR.
