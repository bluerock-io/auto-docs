(*|
In this document, we demonstrate how to specify a class.

We specify a class in three steps:

1. We write the **model** of the class, i.e. what a value of this class "means"
at an intuitive, abstract level.
2. We write the **representation predicate** of the class, i.e. how the model is
implemented using C++ resources.
3. We specify the member functions using the representation predicate.
|*)

(*@HIDE@*)
(*| Here, we demonstrate how to verify a class
First we setup our automation. |*)
Require Import bluerock.auto.cpp.prelude.proof.

(*| Import a command to specify our C++ program "inline". |*)
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
(*@END-HIDE@*)

(*|
## The Program

Here, we define the AST `source` containing our example C++ program: |*)
cpp.prog source prog cpp:{{
  struct IntCell {
    int n{0};
    void method() const {}
    IntCell() = default;
    IntCell(int _n): n(_n) {}
  };

  void test() {
    IntCell m;
    m.method();
  }
}}.

(*|
## The Model

To formalize the type `IntCell`, we define a type `IntCellT` as the _model_ of `IntCell`. A value
of type `IntCellT` describes the data inside an instance of `IntCell`.
Since `IntCell` is a C++ struct with one field of type `int`,
and we use Rocq type `Z` of signed integers as model for `int` (via
representation predicate `intR`),
our model will be a Rocq record with one field of type `Z`.
|*)
Record IntCellT := MkT {
  foo_n : Z
}.

(*@HIDE@*)
(*| Open a Rocq section, that abstracts over some assumptions. |*)
Section with_cpp.
  (*| Separation logic statements depend on an instance of the [cpp_logic] typeclass. |*)
  Context `{Σ : cpp_logic}.
  (*| Specs and proofs also require us to assume that the linked program [σ] contains
  the concrete AST [source] that we're doing proofs about.
  We know nothing else about the program. |*)
  Context `{MOD : source ⊧ σ}.
(*@END-HIDE@*)

  (*|
  ## The Representation Predicate

  In [state basics](../../state_basics/main) we saw how `intR` lets us represent the state
  of a variable of type `int`. That is, `intR` is the representation predicate for type `int`.

  Next, we define the representation predicate for class `IntCell`.
  This will be a function `IntCellR : cQp.t -> IntCellT -> Rep`.

  Assertion `p |-> IntCellR q m` gives ownership `q` of a `IntCell` instance whose content matches the
  model `m`, living at location `p`. Concretely, we define `IntCellR` as follows:
  |*)
  Definition IntCellR (q : cQp.t) (m : IntCellT) : Rep :=
    _field "IntCell::n" |-> intR q m.(foo_n) **
    structR "IntCell" q.
  (*|
  This definition describes the layout of type `IntCell`.
  In many cases, such representation predicate can be generated, but we define
  it ourselves to explain how these work.

  We use `intR q m.(foo_n)` because field `IntCell::n` contains an
  integer with value `m.(foo_n)`.
  We offset that representation predicate with `_field "IntCell::n"` because this
  integer does not live at location `p` (which points to the whole object) but
  at location `p ,, _field "IntCell::n"`.

  This works because when we define a `Rep`, the `x |-> R` operator is
  overloaded to expect `x` to be a pointer _offset_ `o` instead of a pointer.

  `structR "IntCell" q` means we own `q` fraction of a `IntCell` instance; `structR` is
  used for all `struct` and `class` aggregate C++ types.
  |*)

  (*@HIDE@*)
  (* TODO: I want to show br.lock, not this, but it's too early for [br.lock]. *)
  #[global] Hint Opaque IntCellR : br_opacity typeclass_instances.
  (*@END-HIDE@*)

  (*|
  ## The Specifications

  Next, we specify `IntCell` constructors, destructor, and methods.

  Such specifications typically need to refer to the object being constructor,
  destructed, or on which the method is being invoked --- the _receiver_.
  To that end, they can use `\this p` and then for instance `p |-> IntCellR
  1$m m`. `\this p` binds pointer `p` to the receiver object in the rest of the
  spec, and `p |-> IntCellR 1$m m` asserts full ownership of that object.

  First, we specify the default constructor.
  |*)
  cpp.spec "IntCell::IntCell()" as default_ctor_spec with (
    \this this
    \post this |-> IntCellR 1$m (MkT 0)).
  (*|
  Invoking any constructor returns full ownership `1$m` to a new object.
  The `IntCell` default constructor initializes `IntCell::m` to `0`, so the
  default model for the new object is `MkT 0`.

  Next we specify a non-default constructor `IntCell(int)`; this spec is
  similar, but `IntCell(n)` will produce an object with model `MkT n` instead of
  `MkT 0`. `\arg{n} "_n" (Vint n)` binds the C++ argument `_n`'s value to the
  variable `n`.
  |*)
  cpp.spec "IntCell::IntCell(int)" as int_ctor_spec with (
    \this this
    \arg{n} "_n" (Vint n)
    \post this |-> IntCellR 1$m (MkT n)).

  (*|
  Conversely, `IntCell`'s destructor consumes full ownership `1$m` of a `IntCell`
  instance with any model, and returns no ownership. |*)
  cpp.spec "IntCell::~IntCell()" as dtor_spec with (
    \this this
    \pre{m} this |-> IntCellR 1$m m
    \post emp).

  (*| Next, we have the specification of a method that does nothing.
  `\prepost P` means that `P` is used in both the pre-condition and the post-condition of the specification. |*)
  cpp.spec "IntCell::method() const" as method_spec with (
    \this this
    (* Since this method does _not_ modify its receiver, this method doesn't
    need full ownership of [IntCellR] and just borrows partial ownership [q].
    *)
    \prepost{q m} this |-> IntCellR q m
    \post emp).

  cpp.spec "test()" as test_spec with (
    \post emp).

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
