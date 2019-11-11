From Perennial.go_lang Require Import lang notation.

Inductive ty :=
| intT
| byteT
| boolT
| unitT
| prodT (t1 t2: ty)
| arrowT (t1 t2: ty)
| refT (t: ty)
.

Reserved Notation "Γ ⊢ e : A" (at level 91, e at next level, A at level 90).
Reserved Notation "Γ '⊢v' v : A" (at level 91, v at next level, A at level 90).

Definition Ctx := string -> option ty.
Instance empty_ctx : Empty Ctx := fun _ => None.
Instance ctx_insert : Insert binder ty Ctx.
Proof.
  hnf.
  exact (fun b t => match b with
                 | BNamed x => fun Γ => fun x' => if String.eqb x x'
                                           then Some t
                                           else Γ x'
                 | BAnon => id
                 end).
Defined.
Instance ctx_lookup : Lookup string ty Ctx := fun x Γ => Γ x.

Section go_lang.
  Context {ext:ext_op}.

  Inductive base_lit_hasTy : base_lit -> ty -> Prop :=
  | int_hasTy x : base_lit_hasTy (LitInt x) intT
  | byte_hasTy x : base_lit_hasTy (LitByte x) byteT
  | bool_hasTy x : base_lit_hasTy (LitBool x) boolT
  | unit_hasTy : base_lit_hasTy (LitUnit) unitT
  (* hmm seems like locs need to track the type they came from or the
  type-checking doesn't really work *)
  (* maybe we don't need a rule for locs at all? *)
  | loc_hasT t l : base_lit_hasTy (LitLoc l) (refT t)
  .

  (* TODO: this structure doesn't quite work since Eq is polymorphic *)
  Definition bin_op_ty (op:bin_op) : option (ty * ty * ty) :=
    match op with
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp => Some (intT, intT, intT)
    | LtOp | EqOp | LeOp => Some (intT, intT, boolT)
    | _ => None
    end.

  Inductive expr_hasTy (Γ: Ctx) : expr -> ty -> Prop :=
  | var_hasTy x t :
      Γ !! x = Some t ->
      Γ ⊢ Var x : t
  | app_hasTy f x t1 t2 :
      Γ ⊢ f : arrowT t1 t2 ->
      Γ ⊢ x : t1 ->
      Γ ⊢ (App f x) : t2
  | val_expr_hasTy v t :
      val_hasTy Γ v t ->
      Γ ⊢ (Val v) : t
  | rec_expr_hasTy f x e t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e : t2 ->
      Γ ⊢ Rec f x e : arrowT t1 t2
  | offset_op_hasTy e1 e2 t :
      Γ ⊢ e1 : refT t ->
      Γ ⊢ e2 : intT ->
      Γ ⊢ BinOp OffsetOp e1 e2 : refT t
  | bin_op_hasTy op e1 e2 t1 t2 t :
      bin_op_ty op = Some (t1, t2, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ BinOp op e1 e2 : t
  | pair_hasTy e1 e2 t1 t2 :
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ Pair e1 e2 : prodT t1 t2
  | fst_hasTy e t1 t2 :
      Γ ⊢ e : prodT t1 t2 ->
      Γ ⊢ Fst e : t1
  | snd_hasTy e t1 t2 :
      Γ ⊢ e : prodT t1 t2 ->
      Γ ⊢ Snd e : t2
  | if_hasTy cond e1 e2 t :
      Γ ⊢ cond : boolT ->
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      Γ ⊢ (If cond e1 e2) : t
  | alloc_hasTy n v t :
      Γ ⊢ n : intT ->
      Γ ⊢ v : t ->
      Γ ⊢ (AllocN n v) : (refT t)
  | load_hasTy l t :
      Γ ⊢ l : (refT t) ->
      Γ ⊢ (Load l) : t
  | store_hasTy l v t :
      Γ ⊢ l : (refT t) ->
      Γ ⊢ v : t ->
      Γ ⊢ (Store l v) : unitT
  where "Γ ⊢ e : A" := (expr_hasTy Γ e A)
  with val_hasTy (Γ: Ctx) : val -> ty -> Prop :=
  | val_base_lit_hasTy v t :
      base_lit_hasTy v t -> val_hasTy Γ (LitV v) t
  | val_pair_hasT v1 v2 t1 t2 :
      Γ ⊢v v1 : t1 ->
      Γ ⊢v v2 : t2 ->
      Γ ⊢v PairV v1 v2 : prodT t1 t2
  | rec_val_hasTy f x e t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e : t2 ->
      Γ ⊢v RecV f x e : arrowT t1 t2
  where "Γ ⊢v v : A" := (val_hasTy Γ v A)
  .

  Theorem rec_expr_hasTy_eq Γ Γ' f x e t1 t2 :
    Γ' = (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ->
    Γ' ⊢ e : t2 ->
    Γ ⊢ Rec f x e : arrowT t1 t2.
  Proof.
    intros; subst; econstructor; eauto.
  Qed.

End go_lang.

From Perennial.go_lang Require Import slice.
Definition sliceT t : ty := prodT (refT t) intT.

Module slice_types.
Section go_lang.
  Context {ext:ext_op}.
  Notation "Γ ⊢ e : A" := (expr_hasTy Γ e A).

  Opaque Z_to_byte.
  Opaque Z_to_u64.

  Theorem insert_anon t : (<[BAnon := t]> : Ctx -> Ctx) = (fun Γ => Γ).
  Proof.
    reflexivity.
  Qed.

  Ltac simp := unfold For; simpl; rewrite ?insert_anon.
  Ltac type_step :=
    match goal with
    | [ |- expr_hasTy _ _ _ ] => econstructor
    | [ |- expr_hasTy _ (Rec _ _ _) (arrowT _ _) ] => eapply rec_expr_hasTy_eq
    | [ |- val_hasTy _ _ _ ] => econstructor
    | [ |- base_lit_hasTy _ _ ] => econstructor
    end; simp.

  Ltac typecheck :=
    repeat (type_step; try match goal with
                           | [ |- _ = _ ] => cbv; reflexivity
                           end).

  Theorem NewByteSlice_t : ∅ ⊢ NewByteSlice : arrowT intT (sliceT byteT).
  Proof.
    typecheck.
  Qed.

  Theorem MemCpy_t t : ∅ ⊢ MemCpy :
      (* refT t -> refT t -> intT -> unitT *)
      arrowT (refT t)
             (arrowT (refT t)
                     (arrowT intT unitT)).
  Proof.
    typecheck.
  Qed.
End go_lang.
End slice_types.
