(*@@
# Stepping Through Functions

In this tutorial we will learn how to use BlueRock's automation to step
through functions and verify them line-by-line.

We'll consider the following function with the specification written in
the documentation comment.

```cpp
/**
 * \post emp
 */
void test() {
  int x = 0;
  x++;
  x--;
}
```

To understand this, we'll use BlueRock's automation to teach us about
the representation of the program state and how it evolves.
*)
(*@HIDE@*)
(* Setup the verification environment. *)
Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

(* the code *)
cpp.prog source prog cpp:{{
  void test() {
    int x = 0;
    x++;
    x--;
  }
}}.

(* open the section *)
Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}.

  (* the specification of the function *)
  cpp.spec "test()" from source as test_spec with
      (\post emp).
(*@END-HIDE@*)

(*@@
## Exploring a C++ Function with BlueRock Automation

With the specification setup, we can start to step through the program using
the BlueRock automation. The automation is structured to work like symbolic
debugger. To set it up, we set up a proof of the function:
*)
  Lemma test_ok : verify[source] "test()".
  Proof.
    verify_spec.
(*@@
At this point, the goal is looks like the following

```coq
  _ : denoteModule source  (* < the program that we are working with *)
  --------------------------------------□
  _ : PostCond             (* < the post condition, we'll need this later *)
  --------------------------------------∗
  ::wpS  (* < running a statement *)
    [region: return {?: "void"}] (* < the variables in scope *)
    (Sseq 
       [Sdecl [Dvar "x" "int" (Some (Eint 0 "int"))]; Sexpr (core.Epostinc (Evar "x" "int") "int");
        Sexpr (core.Epostdec (Evar "x" "int") "int")])
```


Just like a debugger, we can step forward in the program using the
`run1` tactic which will try to prove that the next step of the program is safe
and step through it.
*)
  run1.
(*@@
This invocation took us to the evaluation of the integer constant `0` that is
the initializer for `x`. We can continue to step through the program with more
invocations of `run1`, then complete the proof with `Qed`.
If we are just exploring, and want to abort the proof, we can use `Abort` instead of `Qed`.
 *)
  run1.
(*@@
After we complete the initialization, note that we get access to the ownership of the
`x` variable. In particular, the goal reads:

```coq
  _ : x_addr |-> intR 1$m 0
  --------------------------------------∗
  ::wpS [region: "x" @ x_addr; return {?: "void"}] (Sexpr (Epostinc (Evar "x" "int") "int"))
```

Above the line, we have the current state, i.e. full ownership of the program location for
the variable `x` (`x_addr` corresponds to the pointer `&x` in C++).
Below the line, we see that we are evaluating the post-increment expression (`x++`).

We can now continue stepping through the program. It takes three steps to get through the
post-increment.
 *)
  run1. (* start evaluating the expression statement *)
  run1. (* evaluate `x` *)
  run1. (* evaluate the post-increment *)
(*@@
At this point, we see that the value of `x` has been updated to `1` (though this form is unreduced), and we are left to prove the decrement.

```coq
  _ : x_addr |-> intR 1$m (0 + 1)
  --------------------------------------∗
  ::wpS [region: "x" @ x_addr; return {?: "void"}] (Sexpr (Epostdec (Evar "x" "int") "int"))
```

Another 3 `run1`s will get us through the decrement.
*)
  run1.
  run1.
  run1.
(*@@
Now, we can see the value of `x` is updated one more time.

```coq
  _ : x_addr |-> intR 1$m (1 - 1)
  --------------------------------------∗
  destroy_val source "int" x_addr (∀ p : ptr, p |-> primR "void" 1$m Vvoid -∗ ▷ _PostPred_ p)
```

At this point, we have reached the end of the function source code, but we are not quite done yet.
In particular, we still need to destroy all of the stack allocated variables.
Even though there are no destructors to run, the C++ machine must take the stack resources back which is captured by `destroy_val`.
In particular, this says that we need to destroy an `int` value at the location `x_addr`.
Again, we can step through this with `run1`.
 *)
  run1.
(*@@
In this case, `run1` not only stepped through the deallocation, but it also finished the proof so we don't get to see the final state.
While this says that the post-condition was provable, it doesn't really let us **see** the final state.
To see the final state, we can undo the last action and then take even smaller steps using the `step` tactic.
 *)
  Undo.
  step. (* take a smaller step *)
(*@@
After the smaller step, we see that the ownership of `x_addr` has been "consumed" by the `destroy_val` step.
Though there is still some complexity in the goal.
Here that complexity is due to the way that values (including `void` "values") are returned; however,
we won't go into that detail here.
In general, while `step` is useful to see the fine-grained reasoning steps that the automation is using, it sometimes exposes internal details of the semantics that are not stable.
In such cases, it is often useful to simply run `step` again to try to simplify the goal.

We can continue to step using `step`, `run1`, or `go`.
 *)
  run.
(*@@
This finishes the proof allowing us to close the proof with `Qed`; however, in many cases during this sort of exploration we will not be able to close the proof, e.g. because there is a bug in the specification.
If we want to keep the debugging proof script intact, we can use the `Abort` command to exit the proof without finishing it.
 *)
Abort.

(*@HIDE@*)
End with_cpp.
(*@END-HIDE@*)
