Require Import bluerock.auto.cpp.prelude.proof.

(*@HIDE@*)

(*@@ Import a command to specify our C++ program "inline". *)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
  class Lock {
    public:
    void lock();
    void unlock();
  };


  void test() {
    Lock m;
    // Lock m{};
    m.lock();
    m.unlock();
  }
}}.

Notation T := "Lock"%cpp_name.

Inductive model : Type := Mk { n : N }.
Definition empty : model := {| n := 0%N |}.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  Parameter R : cQp.t -> model -> Rep.

  cpp.spec (dtor T) as dtor_spec with
    (\this this
     \pre{m} this |-> R 1$m m
     \post emp).

  cpp.spec "Lock::lock()" as lock_spec with
    (\this this
     \prepost{q m} this |-> R q m
     \post emp).

  cpp.spec "Lock::unlock()" as unlock_spec with
    (\this this
     \prepost{q m} this |-> R q m
     \post emp).

  cpp.spec "test()" as test_spec with
    (\post emp).

  cpp.spec (default_ctor T) as ctor_spec with
    (\this this
     \post this |-> R 1$m empty).


  (* Search primR anyR. *)
  Lemma test_ok : verify[source] test_spec.
  Proof.
    Set Warnings "-br-cannot-extract-hint-name".
    verify_spec; go.
#[only(cfracsplittable)] derive R.

    Fail progress work.
#[global] Declare Instance mutex_rep_learnable : LearnEqF1 R.

    progress work.

#[only(type_ptr=T)] derive R.
#[only(type_ptr="Lock")] derive R.
    #[global] Declare Instance R_agree : Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) R).

(* #[only(typed("Lock")] derive R. *)
#[global] Declare Instance mutex_rep_typed : Typed2 "std::__1::mutex" mutexR.
#[only(fracsplittable)] derive mutex_token.

      (* Show Proof. *)
  Qed.
End with_cpp.
