(*
 * Copyright (C) 2022-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.demo.inline.inline_hpp.

Import auto_frac.

#[local] Open Scope Z_scope.

(*| In in some instances, the most natural reasoning principle for a
function is simply to unfold it. In this case, we can use the `inline`
specification to the `cpp.spec` command to generate an specification
for the function automatically.

```coq
cpp.spec "foo()" as foo_inline inline.
```

:::warn
Marking a function for inlining in the logic effectively requires
re-verifying the fuction body every time that the function is called.
This can be expensive, so large functions, and functions that are called
may times should probably use explicitly written function specifications.
:::
:::info
On the other hand, marking a function for inlining in the C++ program using
the `inline` keyword **does not** affect the verification.
:::
|*)

Section with_Σ.
  Context `{Σ:cpp_logic} `{MOD : inline_hpp.source ⊧ σ}.

  Definition CR : Rep :=
    structR "C" 1$m.

  cpp.spec "C::inline_O()" inline.
  cpp.spec "C::inline_L(int&)" as inline_L inline.
End with_Σ.

Section with_Σ.
  Context `{Σ:cpp_logic, σ : genv} `{MOD : inline_hpp.source ⊧ σ}.

  cpp.spec "C::inline_I()" inline.

  cpp.spec "C::inline_X(int&)" as inline_X from (inline_hpp.source) inline.
  cpp.spec "inline_O()" inline.
  cpp.spec "inline_X(int&)" inline.
  cpp.spec "inline_L(int&)" inline.
  cpp.spec "inline_I()" inline.
  cpp.spec "into_L(int&)" inline.
  cpp.spec "into_X(int&&)" inline.

  cpp.spec "C::C()" inline.
  cpp.spec "C::~C()" inline.

  (* Tip: When function names include a <<* )>>, it can be useful to
     put a space between then to distinguish them from end-of-comments markers.
   *)
  cpp.spec "test(C* )" as test_spec with
    (\arg{p} "" (Vptr p)
     \prepost p |-> CR
     \post emp).

  Lemma test_ok : denoteModule inline_hpp.source |-- test_spec.
  Proof using MOD.
    verify_spec. go with pick_frac.
  Qed.

End with_Σ.
