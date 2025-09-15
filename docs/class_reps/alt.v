(*@HIDE@*)
(*|
First we setup our automation and use an example program: |*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
Implicit Type (σ : genv).
(*@END-HIDE@*)

NES.Begin Point.

(*|
## Class Representation predicates

Consider the following AST `source`, definining C++ class `Point`.
|*)
cpp.prog source prog cpp:{{
  class Point {
    int x;
    int y;
  };
}}.

(*|
Just like `intR` defines the memory representation for the type `int`,
we can define `PointR` to define the memory representation for the class `Point`.
The following assertion describes a struct of type `Point` where field `x`
contains the integer `1` and field `y` contains the integer value `5`: |*)

Example R15 `{Σ : cpp_logic} {σ} (q : cQp.t) : Rep :=
  structR "Point" q **
  _field "Point::x"  |-> intR q 1 **
  _field "Point::y"  |-> intR q 5.


(*|
The above was too concrete; it stored the specific point `(1, 5)`.
Just like `intR` takes as agument a `z : Z` to denote the mathematical number being
represented, we define a Gallina record type `t` to denote the mathematical model of what is stored:
|*)

Record t : Type := Mk
{ p_x : Z
; p_y : Z
}.

(** Then we can define the general class representation as follows: *)
br.lock
Definition R `{Σ : cpp_logic} {σ} (q : cQp.t) (m : t): Rep :=
  structR "Point" q **
  _field "Point::x"  |-> intR q m.(p_x) **
  _field "Point::y"  |-> intR q m.(p_y).

(*| We derive some utility infrastructure to be used later. |*)
#[only(cfracsplittable)] derive R.
#[only(type_ptr=Point)] derive R.
Module R_Unfold.
  #[only(lazy_unfold(export))] derive R.
End R_Unfold.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ}.

  cpp.spec (default_ctor "Point") from source as ctor_spec with (
    \this this
    \post this |-> R 1$m (Mk 0 0)
  ).

  Section with_R_Unfold.
    Import R_Unfold.

    Lemma ctor_ok : verify[source] ctor_spec.
    Proof.
      verify_spec; go.
      Import MyPretty.
      Show.
(*|
Here, the proof is stuck.
Sometimes, that means that our automation needs help to complete the proof.
But here, our program does not implement our specification, so one of the two is buggy.

More specifically, this is the goal:
```coq
  _ : this ,, o_field σ "Point::x" |-> uninitR "int" 1$m
  _ : this ,, o_field σ "Point::y" |-> uninitR "int" 1$m
  --------------------------------------∗
  this ,, o_field σ "Point::y" |-> intR 1$m 0 ∗ this ,, o_field σ "Point::x" |-> intR 1$m 0
```

Our current state says that fields `x` and `y` are not initialized, while our goal
requires them being initialized.

More specifically, pointer `this ,, o_field σ "Point::x"` (in C++, `&(this->x)`) points to
`uninitR "int" 1$m` in the assumption, and to `intR 1$m 0` in the goal.
Same for `this ,, o_field σ "Point::y"` (in C++, `&(this->y)`).

To continue, we abort the proof, and define AST `source1` with a fixed version of the code.
|*)
    Abort.

    cpp.prog source1 prog cpp:{{
      class Point {
        int x{0};
        int y{0};
      };
    }}.

    (*|
    In the fixed AST `source1`, `Point`'s implicitly generated constructor will
    initialize fields `x` and `y` to `0`.
    We can then easily prove `Point`'s constructor correct against the new AST.
    |*)

    Lemma ctor_ok : verify[source1] ctor_spec.
    Proof.
      verify_spec; go.
    Qed.
  End with_R_Unfold.
End with_Σ.

NES.End Point.
