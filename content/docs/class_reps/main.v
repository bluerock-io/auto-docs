(*@@
In this document, we demonstrate how to specify a class.

We specify a class in three steps:

1. We write the **model** of the class, i.e. what a value of this class "means"
at an intuitive level.
2. We write the **representation predicate** of the class, i.e. how the model is
implemented in the C++ source code.
3. We specify the member functions using the representation predicate.
*)

(*@HIDE@*)
(*@@ Here, we demonstrate how to verify a class
First we setup our automation. *)
Require Import bluerock.auto.cpp.prelude.proof.

(*@@ Import a command to specify our C++ program "inline". *)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
(*@END-HIDE@*)

(*@@ Here, we define AST `source` containing our example C++ program: *)
cpp.prog source prog cpp:{{
  struct Foo {
    int n{0};
    void method();
  };

  void test() {
    Foo m;
    m.method();
  }
}}.

(*@@
## The Model

To formalize type `Foo`, we define a type `FooT` of _models_ of `Foo`. A value
of type `FooT` describes the data inside an instance of `Foo`. *)
Record FooT := MkT {
  foo_n : Z
}.

(*@HIDE@*)
(*@@ Open a Rocq section, that abstracts over some assumptions. *)
Section with_cpp.
  (*@@ Separation logic statements depend on an instance of the [cpp_logic] typeclass. *)
  Context `{Σ : cpp_logic}.
  (*@@ Specs and proofs also require us to assume that the linked program [σ] contains
  the concrete AST [source] that we're doing proofs about.
  We know nothing else about the program. *)
  Context `{MOD : source ⊧ σ}.
(*@END-HIDE@*)

  (*@@
  ## The Representation Predicate

  In [state basics](../../state_basics/main) we saw how `intR` lets us represent the state
  of a variable of type `int`. That is, `intR` is the representation predicate for type `int`.

  Next, we define the representation predicate for class `Foo`.
  This will be a function `FooR : cQp.t -> FooT -> Rep`.

  Assertion `p |-> FooR q m` gives ownership `q` of a `Foo` instance whose content matches the
  model `m`, living at location `p`. Concretely, we define `FooR` as follows:
  *)
  Definition FooR (q : cQp.t) (m : FooT) : Rep :=
    _field "Foo::n" |-> intR q m.(foo_n) **
    structR "Foo" q.
  (*@@
  This definition describes the layout of type `Foo`.
  In many cases, such representation predicate can be generated, but we define
  it ourselves to explain how these work.

  We use `intR q m.(foo_n)` because field `Foo::n` contains an
  integer with value `m.(foo_n)`.
  We offset that representation predicate with `_field "Foo::n"` because this
  integer does not live at location `p` (which points to the whole object) but
  at location `p ,, _field "Foo::n"`.

  This works because when we define a `Rep`, the `x |-> R` operator is
  overloaded to expect `x` to be a pointer _offset_ `o` instead of a pointer.

  `structR "Foo" q` means we own `q` fraction of a `Foo` instance; `structR` is
  used for all `struct` and `class` aggregate C++ types.
  *)

  (*@HIDE@*)
  (* TODO: I want to show br.lock, not this, but it's too early for [br.lock]. *)
  Hint Opaque FooR : br_opacity typeclass_instances.
  (*@END-HIDE@*)

  (*@@ Specify `Foo`'s constructor and destructor. *)
  cpp.spec (default_ctor "Foo") as ctor_spec with
    (\this this
     (* After invoking `Foo`'s constructor on `this`,
      we have full ownership `1$m` of a `Foo` instance,
      whose model is `MkT 0`.
      *)
     \post this |-> FooR 1$m (MkT 0)).

  (*@@ Conversely, `Foo`'s destructor consumes full ownership of a `Foo`
  instance with any model. *)
  cpp.spec (dtor "Foo") as dtor_spec with
    (\this this
     \pre{m} this |-> FooR 1$m m
     \post emp).

  (*@@ Here we have the specification of a method that does nothing. *)
  cpp.spec "Foo::method()" as method_spec with
    (\this this
     \prepost{q m} this |-> FooR q m
     \post emp).

  cpp.spec "test()" as test_spec with
    (\post emp).

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
