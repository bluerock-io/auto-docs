(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.

Section with_cpp.
Context `{cpp_logic} {σ : genv}.
(*@END-HIDE@*)
(*|
Read-only sharing of data is pervasive in programs from small to large.
Limiting mutability is especially crucial when avoiding data races in concurrent programs since these lead to [undefined behavior](todo); however, fine-grained, sequential immutability is a powerful tool when building and reasoning about programs.

## Fractional Permissions

The most common way to describe sharing of resources in separation logic is using fractional permissions.
Rather than having complete ownership of a resource, e.g. a program location, you can have a (fractional) part of the ownership and other threads or data structures can own the other parts.

Consider the `primR` representation predicate for describing an initialized program location storing a primitive.
We can check the type of this using
|*)
Check primR.
(* primR : type → cQp.t → val → Rep *)

(*|
The second to last argument is a `cQp.t` which is a (`const`-annotated, the `c`) positive fraction (the `Qp`).
For the purpose of sharing, we'll focus only on the `Qp`.
When we write these in the common notation, we use `q$m` or `q$c`, `q` is the fraction.

## Dividing Ownership
The benefit of using fractions is that they can easily be split up and re-combined.
For example, if we have full ownership of an integer, we can divide it into two parts and give those two parts to different threads or data abstractions.
Formally, this is demonstrated by the following:
|*)
Goal forall (p : ptr) (z : Z),
  p |-> intR 1$m z
  |-- p |-> intR (1/2)$m z ** p |-> intR (1/2)$m z.
Proof. work. Qed.

(*|
This process can be repeated arbitrarily.
Generalizing the theorem above, we see
|*)

Goal forall (p : ptr) (q : Qp) (z : Z),
  p |-> intR q$m z
  |-- p |-> intR (q/2)$m z ** p |-> intR (q/2)$m z.
Proof. work. Qed.

(*|
This also works out for spitting into other numbers of pieces, e.g. if we want to share a value between three threads, we can divide it into three equal parts.
|*)

Goal forall (p : ptr) (q : Qp) (z : Z),
  p |-> intR q$m z
  |-- p |-> intR (q/3)$m z ** p |-> intR (q/3)$m z ** p |-> intR (q/3)$m z.
Proof. work. Qed.

(*|
:::info
Symmetric fractions are often quite easy to work with, but it can also be helpful to distinguish between two parts, e.g. if the main thread retains some ownership and gives other ownership to workers.
To capture this pattern, it is common to use non-symmetric fractions, e.g. the main thread retains `2/3` ownership while the worker thread gets `1/3` ownership.
:::

## Combining Ownership
In addition to splitting, ownership can also be combined.
|*)
Goal forall (p : ptr) (q : Qp) (z : Z),
  p |-> intR (q/2)$m z ** p |-> intR (q/2)$m z
  |-- p |-> intR q$m z.
Proof. work. Qed.
(*|

In general, all of the theorem that we proved in the previous section also hold for combining.

## Consistency
A crucial property of fractional ownership is that all of the ownership must be _consistent_.
Concretely, if I have two fractions of ownership of the same location at unknown values, then those to values must be the same.
This is demonstrated by the following theorem:

|*)
Goal forall (p : ptr) (q : cQp.t) a b,
  p |-> intR (q / 2)$c a ** p |-> intR (q / 2)$c b
  |-- [| a = b |] ** p |-> intR q$c a (* equivalently <<intR q b>> *).
Proof. (* ... proof elided ... *) (*@HIDE@*)
  iIntros (????) "[H1 H2]".
  iDestruct (observe_2 [| _ = _ |] with "H1 H2") as "%".
  inversion H0; subst. work $usenamed=true.
(*@END-HIDE@*)Qed.
(*|

Consistency is a powerful reasoning feature when reasoning through abstractions and concurrent invariants, but in simple sequential code it is mostly unnecessary.

## "Full" Ownership & Fractional Validity
It is common to talk about fraction 1 as "full ownership".
This is because the fractional ownership of an object is constrained to be **greater than** 0 and **less than or equal** to 1[^fraction-validity].

Concretely, this can be seen in the following theorem:
|*)
Goal forall (p : ptr) q (z : Z),
  p |-> intR q$c z |-- [| (0 < toQ q)%Q ∧ (q ≤ 1)%Qp |] ** True.
Proof. (* ... proof elided ... *)(*@HIDE@*)
  iIntros (???) "H"; iDestruct (observe [| Qp.le _ _ |] with "H") as "%".
  iPureIntro. intuition eauto. clear -q.
(*@END-HIDE@*) Abort.
(*|

This principle is useful when capturing limited sharing.
For example, take a reader-writer lock.
Acquiring read-permission to the lock can yield an unknown amount of ownership and acquiring write permission can yield full ownership.
Using fractional validity, we can prove that it is not possible to simultaneously have a read and write fraction since:

|*)
Goal forall (p : ptr) (q : Qp) z,
  p |-> intR 1$m z ** p |-> intR q$c z |-- False.
Proof. work. Abort.
(*|

:::info
A more idiomatic characterization of reader-writer locks would avoid the `const`-qualification and use only the `Qp`.
:::

[^fraction-validity]: Limiting the fraction to 1 is idiomatic, but not strictly necessary in the core separation logic. This property is captured separately through the `FracValid` typeclass.
|*)

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
