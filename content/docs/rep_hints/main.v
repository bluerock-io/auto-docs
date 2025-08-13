(*| Here, we show some hints about `Rep`s that we can declare to get proofs unstuck.
 First we setup our automation and use an example program: |*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

(*| Define AST `source` containing our example C++ program.
This is the same as in the [earlier tutorial](../../class_reps/main). |*)
cpp.prog source prog cpp:{{
  struct IntCell {
    int n{0};
    void method() const;
  };


  void test() {
    IntCell m;
    m.method();
  }
}}.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  Parameter R : cQp.t -> N -> Rep.

  cpp.spec (default_ctor "IntCell") as ctor_spec with
    (\this this
     \post this |-> R 1$m 0).

  cpp.spec (dtor "IntCell") as dtor_spec with
    (\this this
     \pre{m} this |-> R 1$m m
     \post emp).

  cpp.spec "IntCell::method() const" as method_spec with
    (\this this
     \prepost{q m} this |-> R q m
     \post emp).

  cpp.spec "test()" as test_spec with
    (\post emp).

  Lemma test_ok : verify[source] test_spec.
  Proof.
    verify_spec; go.
    (*| TODO: explain here the goals we're stuck on, and the hints we need. |*)

    #[global] Declare Instance R_learn : Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) R).
    progress work.
    #[only(cfracsplittable)] derive R.
    progress work.

    #[only(type_ptr="IntCell")] derive R.

    progress work.
    go.
  Qed.
End with_cpp.
