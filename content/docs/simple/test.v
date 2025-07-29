(*@HIDE@*)
Require Import bluerock.auto.cpp.prelude.proof.
(*@END-HIDE@*)
(*@@
# Verifying a simple program

We can start with a very simple program:

```cpp
void test() { }
```

## Writing a Spec

We start with a specification.
 *)
cpp.spec "test()" as test_spec with
  (\post emp).
(*@@
The `emp` tells you that the function doesn't return any {{ "resource" | terminology }}, but we'll get into that more later.

## Verifying the Function

Now, we can set up the verification by posing a `Lemma`.
 *)
Lemma test_ok : verify[source] "test()".
Proof.
(*@@
This sets up a theorem for our function that states that the function satisfies the specification. In this case, this means that executing the function will not produce any {{ "undefined behavior" | terminology }}.

Since this is a particularly simple function, the proof is also simple. This proceeds in two stages:
1. We use `verify_spec` to begin the proof, effectively to reason about connection between the arguments (in this case there are none) to the arguments expressed in the specification.
2. Next we use the `go` tactic to "execute" the body of the function and prove the post-condition.

Idiomatically, we chain these two tactics together using a `;` which leads us to the following proof script.
 *)
  verify_spec; go.
Qed.
(*@@
The `Qed` ends the proof and Rocq tells us that the proof is checked.

Congratulations! You've walked through your first proof.

## What's Next?

Consider verifying some more simple functions including:

 *)
