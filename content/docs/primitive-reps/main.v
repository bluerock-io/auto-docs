(*@HIDE@*)
Require Import bluerock.lang.cpp.cpp.
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
(*@END-HIDE@*)
(*@@
# Primitive Reps

The BRiCk program logic provides several {{ "representation predicates" | terminology }} for
primitive C++ state.

- `primR ty q v` -- initialized program location storing `v` of type `ty` (can not store raw values)
- `uninitR ty q` -- uninitialized program location of type `ty`
- `anyR ty q` -- a program location of type `ty` with completely unknown contents (initialized, uninitialized, or raw)

**Convention**: By convention, representation predicates end with a capital `R`, e.g. `primR`, `fooR`, etc.

## `primR`

The most common predicate for talking about the value at a program location is `primR`.
*)
About primR.
(* primR : type -> cQp.t -> val -> Rep *)
(*@@
`primR ty q v` captures the `q` ownership of the **initialized** program cell with type `ty` and value `v`.
Some examples,
*)

Check primR "int" 1$m (Vint 3).         (* << mutable integer cell containing value 3 *)
Check primR "char" 1$m (Vchar 65).      (* << mutable character cell containing value 'A' *)
Check primR "long int" 1$c (Vint 1000). (* << constant long int cell containing value 1000 *)

(*@@
Because `primR` captures **initialized** program state, it implies that the value stored in the location
(the last argument) is well typed at the type of the location. Formally, this is captured by the following
*)
Lemma primR_has_type : forall (p : ptr) ty q v,
    p |-> primR ty q v |-- validP<ty> v.
Proof. (*@HIDE@*) (* intros. iIntros "H"; iDestruct (observe (has_type _ _) with "H") as "#". *) (*@END-HIDE@*) Admitted.

(*@@
Because `primR` is so common, BRiCk provides notations for the basic types with their canonical type representations.
For example,
*)

Print intR.
Print ulongR.
Print ulonglongR.
Print charR.
Print wchar_tR.

(*@@
## `uninitR` -- Uninitialized Data

Unlike high-level languages, C++ does not mandate that all variables are initialized.
For instance, variable `x` is not initialized in the following code.

```cpp
void f() {
  int x;
BRiCk provides the `Rep`-predicate `uninitR` to capture uninitialized program cells of a particular type.
*)
About uninitR.
(* uninitR : type -> cQp.t -> Rep *)
(*@@
Formally, `uinitR ty q` captures an uninitialized program location of type `ty`.
However, because uninitialized data is often transitory, explicitly writing this predicate is quite rare.
In practice, we often prefer `anyR` to capture a value that may or may not be initialized.
*)

(*@@

## `anyR`

The `anyR` `Rep`-predicate captures a program location that is either initialized or not.
The type of `anyR` is the same as `uninitR`.
*)
About anyR.
(* anyR : type -> cQp.t -> Rep *)
(*@@

*)
