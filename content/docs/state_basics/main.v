(*|
# The Program State

In this tutorial we will focus on the very basics of {{ "separation logic" | terminology }},
primarily on primitive types. Separation logic is a logic of {{ "resource" | terminology }} that can be "owned".
While this concept is somewhat abstract, seeing a few examples should clarify things.

Consider the following program with a comment representing the program state at each line.

```cpp
void test() {
   // emp
  int x = 0;
   // _local "x" |-> intR 1$m 0
  x++;
   // _local "x" |-> intR 1$m 1
}
```

In the first line, there are no variables, so the state is empty, so we write `emp`.

After the first line runs, there is now a new "program location" allocated. That program
location is the cell that stores the value of the variable `x`. The location has type
`int`, and the value stored in the cell is `0`. This state is captured by the second line:

```coq
_local "x" |-> intR 1$m 0
```

The `|->` is the "points-to" operator which takes a left-hand-side that is a pointer
and the right-hand-side describing a portion of the program state at that pointer.
The `_local "x"` is effectively the pointer `&x`. The right hand side, `intR 1$m 0`,
represents a mutable program location of type `int` with value `0`.
(The `1` in `1$m` is a {{ "fraction" | terminology }}, used to specify {{
"fractional ownership" | terminology }}, but we will ignore it
for now and always use `1`.)

Incrementing `x` changes the value stored in the cell. The resulting state is described
by the following assertion.

```coq
_local "x" |-> intR 1$m 1
```

Here, the pointer did not change, but the value stored at the pointer changed
from `0` to `1`.

## Multiple Locations

Now suppose that we declare a new variable.

```cpp
int y = 10;
```

Similarly to what we've seen, the state of `y` after this declaration is captured by

```coq
_local "y" |-> intR 1$m 10
```

However, the full program state contains **both** of these program locations. To capture
multiple **disjoint** program locations, we connect the two assertions using a `**` (or in unicode `∗`).
The `**` is called the "separating conjunction" and is pronouned "star".
Thus, the full state after this declaration is captured by

```coq
_local "x" |-> intR 1$m 1 ** _local "y" |-> intR 1$m 10
```

The crucial feature of the separating conjunction is that it implicitly captures the disjointness
of the two locations. Without the disjointness, we would need to explicitly state that
`_local "x"` does not equal `_local "y"`. In this case, explicitly stating the disjointness would
not be overly cumbersome, but as the number of pointers grows and abstractions hide internal pointers,
explicit disjointness without separation logic quickly becomes intractable.

## The Frame Rule

The benefit of disjointness is that it enables highly modular reasoning. For example, suppose
that we now increment the value of `y`, i.e.

```cpp
y++;
```

To reason about this step, we only need to think about the "program cell" for `_local "y"`, i.e.
the resource `_local "y" |-> intR 1$m 10`. We call this resource the "footprint" of the step.
The other resources, in this case `_local "x" |-> intR 1$m 1` are called the "frame".
In general, the footprint of a step __can__ change, while the frame stay __unchanged__.
Thus, after the update, the state looks like the following:

```coq
_local "x" |-> intR 1$m 1 ** _local "y" |-> intR 1$m 11
```

## Recap

With this we have seen the basics of how separation logic works in a very small example.
See the [Further Reading](../../further-reading) section for more materials on separation logic.
|*)

(*@HIDE@*)
(* See {{ "separation logic" | terminology }} for more information. *)
(*@END-HIDE@*)
