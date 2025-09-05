(*@HIDE@*)
Require Import bluerock.lang.cpp.cpp.
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
(*@END-HIDE@*)
(*|
# Primitive Reps

The BRiCk program logic provides several {{ "representation predicates" | terminology }} for
primitive C++ state.

- `primR ty q v` -- initialized program location storing `v` of type `ty` (can not store raw values)
- `uninitR ty q` -- uninitialized program location of type `ty`
- `anyR ty q` -- a program location of type `ty` with completely unknown contents (initialized, uninitialized, or raw)

**Convention**: By convention, representation predicates end with a capital `R`, e.g. `primR`, `fooR`, etc.

## `primR`

The most common predicate for talking about the value at a program location is `primR`.
|*)
About primR.
(* primR : type -> cQp.t -> val -> Rep *)
(*|
`primR ty q v` captures the `q` ownership of the **initialized** program cell with type `ty` and value `v`.
Some examples,
|*)

Check primR "int" 1$m (Vint 3).         (* << mutable integer cell containing value 3 *)
Check primR "char" 1$m (Vchar 65).      (* << mutable character cell containing value 'A' *)
Check primR "long int" 1$c (Vint 1000). (* << constant long int cell containing value 1000 *)

(*|
Because `primR` captures **initialized** program state, it implies that
the value (the last argument) stored at the location is well typed at the type of the location.
For instance, a `char` cannot store a `Vint` value, an `int` cannot store a
`Vchar` value, and neither can store a value that overflows the storage.
In other words, even if `val` has "too many" values, `primR ty q v` can rule out
the values of `v` that are not appropriate for `ty`.

Formally, this is captured by the following:
|*)
Lemma primR_has_type : forall (p : ptr) ty q v,
    p |-> primR ty q v |-- validP<ty> v.
Proof. (*@HIDE@*) (* intros. iIntros "H"; iDestruct (observe (has_type _ _) with "H") as "#". *) (*@END-HIDE@*) Admitted.

(*|
Because `primR` is so common, BRiCk provides notations for the basic types with their canonical type representations.
For example,
|*)

Print intR.
Print ulongR.
Print ulonglongR.
Print charR.
Print wcharR.

(*|
## `uninitR` -- Uninitialized Data

Unlike high-level languages, C++ does not mandate that all variables are initialized.
For instance, variable `x` is not initialized in the following code.

```cpp
void f() {
  int x;
  // _local "x" |-> uninitR "int" 1$m
}
```
BRiCk provides the `Rep`-predicate `uninitR` to capture uninitialized program cells of a particular type.
|*)
About uninitR.
(* uninitR : type -> cQp.t -> Rep *)
(*|
Formally, `uinitR ty q` captures an uninitialized program location of type `ty`.
However, because uninitialized data is often transitory, explicitly writing this predicate is quite rare.
In practice, we often prefer `anyR` to capture a value that may or may not be initialized.
|*)

(*|

## `anyR` -- Possibly Uninitialized Data

The `anyR` `Rep`-predicate captures a program location that is either initialized or not.
The type of `anyR` is the same as `uninitR`.
|*)
About anyR.
(* anyR : type -> cQp.t -> Rep *)
(*|
The `anyR` ownership can be particularly useful when describing a program state at the beginning
of a loop. For example, suppose that you have the following `do-while` loop.
```cpp
int x;
// _local "x" |-> uninitR "int" 1$m
do {
  // _local "x" |-> anyR "int" 1$m
  x = f();
} while (x > 0);
```
Before we enter the loop the first time, we know that `x` is uninitialized, but on subsequent
iterations of the loop, `x` might be initialized. To capture this pattern, we can use `anyR`
to say that the loop will execute correctly regardless of whether `x` is initialized or not.
|*)

(*|
## Recap

Here we learned about the three most common predicates for describing primitive data,

1. `primR` for initialized data;
2. `anyR` for data that may or may not be initialized; and
3. `uninitR` for data that is known to be uninitialized.

These predicates alone are sufficient for describing the behavior of many simple programs.
|*)


(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
