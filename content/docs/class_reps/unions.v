Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
Implicit Type (σ : genv).

NES.Begin Unions.
  (*@@
  ## Union Representation predicates

  Sometimes, the interpretation of a piece of data depends on another value.
  For example, consider the following datatypes.
  *)
  cpp.prog source prog cpp:{{
    union untagged {
      int x;
      bool y;

      untagged(int x) {
        this->x = x;
      }
      untagged(bool y) {
        this->y = y;
      }
    };

    struct tagged {
      bool tag;
      untagged u;
    };
  }}.

  (* untagged make_x(int x) { *)
  (*   return {.x = x}; *)
  (* } *)
  (* untagged make_y(bool y) { *)
  (*   return {.y = y}; *)
  (* } *)

  NES.Begin Untagged.

    Variant t : Set :=
    | AnInt (_ : Z) (* a value of type [Z] *)
    | ABool (_: bool) (* a value of type [bool] *).
    (*@@
    Rocq variants are tagged, so we can pattern match on a value of
    type `t` to determine which case it is.
    *)
    (** this has both integers and booleans *)
    Check AnInt 3 : t.
    Check ABool true : t.

    Definition union_variant_id (m : t) : nat :=
      match m with
      | AnInt _ => 0
      | _ => 1
      end.

    Definition is_an_int (m : t) : bool :=
      match m with
      | AnInt _ => true
      | _ => false
      end.

    br.lock
    Definition R `{Σ : cpp_logic} {σ} (q : cQp.t) (m : t): Rep :=
      unionR "untagged" q (Some (union_variant_id m)) **
      match m with
      | AnInt z => _field "untagged::x" |-> intR q z
      | ABool b => _field "untagged::y" |-> boolR q b
      end.

    (*@HIDE@*)
    Definition cfrac_match_match := ().
    #[local] Hint Extern 0 (CFractional (fun a => match ?x with | _ => _ end)) =>
      hint_label cfrac_match_match; destruct x : typeclass_instances.
    (*@END-HIDE@*)

    #[only(cfracsplittable)] derive R.
    #[only(type_ptr=untagged)] derive R.
    Module R_Unfold.
      #[only(lazy_unfold(export))] derive R.
    End R_Unfold.

    Section with_Σ.
      Context `{Σ : cpp_logic} {σ}.
  (* Context `{MOD : source ⊧ σ}. *)

      cpp.spec "untagged::untagged(int)" from source as int_ctor_spec with (
        \this this
        \arg{n} "n" (Vint n)
        \post this |-> R 1$m (AnInt n)
      ).

      cpp.spec "untagged::untagged(bool)" from source as bool_ctor_spec with (
        \this this
        \arg{b} "b" (Vbool b)
        \post this |-> R 1$m (ABool b)
      ).


      (* unionR "untagged" q (Some (union_variant_id m)) ** *)
      (*                   type_ptr "t" *)

      Section with_R_Unfold.
        (* Import R_Unfold. *)

        Lemma int_ctor_ok : verify[source] int_ctor_spec.
        Proof.
          (* Set BR Debug "@default=1". *)
          (* with_log! *)
          verify_spec.
          go.
          (*
- wp_union_initializer_list is buggy: must produce `unionR ty 1$m None ** anyR ty 1$m`
- also missing, support for changing active members through assignment.
           *)
          iAssert(this |-> unionR "untagged" 1$m (Some 0)) as "-#?"%string. { admit. }
          work.
          iAssert(this ., "untagged::x" |-> type_ptrR "int") as "#?"%string. { admit. }

          Remove Hints type_ptr_field_gc_F : br_opacity.

          work.
          iAssert(this ., "untagged::x" |-> anyR "int" 1$m) as "-#?"%string. { admit. }
          work.
          Import R_Unfold.
          Fail progress go.
          rewrite R.unlock.
          by work.
        Succeed Admitted.
        Abort.
      End with_R_Unfold.
    End with_Σ.
  NES.End Untagged.
NES.End Unions.
