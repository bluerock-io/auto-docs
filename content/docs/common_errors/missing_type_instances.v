(*|
Sometimes, a proof will get stuck because the automation
can not prove the a reference is valid. In these cases,
the proof usually gets stuck on a `reference_to<ty> p` obligation.

A contrived program that exhibits this behavior is:

```cpp
struct C {};
void test(C c) {
  C& r{c};
}
```
|*)
(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
  struct C {};
  void test(C c) {
    C& r{c};
  }
}}.

br.lock Definition CR `{Σ : cpp_logic} `{σ : genv} (q : cQp.t) : Rep :=
  structR "C" q.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  cpp.spec "test(C)" with (
    \arg{cr} "c" (Vref cr)
    \prepost{q} cr |-> CR q
    \post emp).
(*@END-HIDE@*)

(*|
This proof gets stuck on the following goal:
 |*)
Lemma test_ok : verify[source] "test(C)".
Proof.
  verify_spec.
  go.
(*|
```coq
  _ : c_addr |-> CR q
  --------------------------------------∗
  reference_to "C" c_addr ∗
  (r_addr |-> refR<"C"> 1$m c_addr -∗
   interp source 1
     (wp_decls source [region: "r" @ r_addr; "c" @ c_addr; return {?: "void"}] []
        (λ (ρ : region) (free' : FreeTemps),
           ▷ wp_block source ρ []
               (Kfree source (free' >*> FreeTemps.delete "C&" r_addr)
                  (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v)))))))
```

The automation is stuck verifying this goal because it can not prove the `reference_to "C" c_addr` obligation.

## Solution: Add a Hint

This is most commonly solved using a `Typed` hint on the class. The following code creates this hint automatically.
|*)
  #[only(type_ptr="C")] derive CR.
(*|
After introducing the hint, the automation can make progress.

In this case, `#[only(type_ptr)] derive CR.` is also sufficient,
because the automation can infer the type `C` from `CR`'s definition.
|*)
  go.
(*@HIDE@*)

(*|
Consult [`reference_to` and `type_ptr` here]() for more information about this
concept.
|*)
  Qed.
End with_cpp.
(*@END-HIDE@*)
