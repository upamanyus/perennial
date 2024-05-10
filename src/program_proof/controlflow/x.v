From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose Require sync. Module mysync := sync.

(* "Exception" monad *)
Definition go_return : val :=
  λ: "v", (#(str "return"), Var "v")
.

Definition do : val :=
  λ: <>, (#(str "noreturn"), #())
.

(* Takes in the return value of the first block and a lambda for the next block
   as a pair. Taking it as a pair (instead of via currying) results in the
   notation working better during printing. With currying, the notation looks
   for (App (App exception_seq ....)). Here, it just needs (App exception_seq ...)
 *)
Definition exception_seq : val :=
  λ: "s1",
    if: ((Fst (Fst "s1")) = #(str "return")) then
      go_return (Snd (Fst "s1"))
    else
      (Snd "s1") #()
.

Definition exception_do : val :=
  λ: "v", Snd "v"
.

Local Notation "e1 ;;; e2" := (exception_seq (e1%E, (Lam BAnon e2%E))%E)
  (at level 100, e2 at level 200,
      format "'[' '[hv' '[' e1 ']' ;;;  ']' '/' e2 ']'") : expr_scope.

Definition test2 : val :=
  λ: <>,
     exception_do (
     let: "x" := ref_zero uint64T #() in
     (if: (#0 = #0) then
        (do ("x" <-[uint64T] #37)) ;;;
        (do ("x" <-[uint64T] ![uint64T] "x" * ![uint64T] "x"))
      else
        go_return #3
     ) ;;;
     (if: ![uint64T] "x" > #13 then
        go_return ![uint64T] "x" ;;;
        do #1 + #(str "unreachable")
      else
       do #()) ;;;
     go_return #3
     )
.

(* ty is needed for zero value, heap points-to, etc. *)
Definition go_ty : Type := ty * (gmap string val).

(*
  func A() {
    B()
  }


  func B() {
    A()
  }
*)

Definition MapGet : val :=
  (rec: "mapGet" "m" "k" :=
     match: "m" with
       InjL "def" => Panic ""
     | InjR "kvm" =>
       let: "kv" := Fst "kvm" in
       let: "m2" := Snd "kvm" in
       if: "k" = (Fst "kv") then (Snd "kv")
       else "mapGet" "m2" "k"
     end).

Definition MapInsert: val :=
  λ: "m" "k" "v", InjR ("k", "v", "m").

Definition MapEmpty: val := InjLV #().

Notation "e1 @ e2" := (MapGet e1 e2)
  (at level 100, e2 at level 200, format "e1 '@' e2") : expr_scope.

(* Notation "func:" *)

Definition bar: val :=
  rec: "$pkg" "$ctx" :=
    (MapInsert
       (MapInsert
          (MapInsert MapEmpty
             #(str "A") (λ: <>, do (Var "$pkg")@"B" #())%E
          )
          #(str "B") (λ: <>,
                  let: "$expr1" := !"$pkg"@#(str"globalVar") in
                  (if: "$expr1" = #1 then
                     go_return #37
                   else do #()
                  ) ;;;
                  do "$pkg"@#(str"globalVar") <-[uint64T] ("$expr1" + #1) ;;;
                  do "$pkg"@#(str"A") #()
              )%E
       )
       #(str "globalVar") (ref_zero uint64T #())
    )
.

From Perennial.program_proof Require Import grove_prelude.
Section proof.
Context `{!heapGS Σ}.

Definition wp_A (A:val) : iProp Σ :=
  WP (A #()) {{ v, ⌜ v = #37 ⌝%I }}.

Definition wp_B (B:val) : iProp Σ :=
  WP (B #()) {{ v, ⌜ v = #37 ⌝%I }}.

Definition own_bar (pkg:val) : iProp Σ :=
  ∃ (globalVar:loc) (v:u64),
  "#HglobalVar" ∷ (□ WP pkg@#(str"globalVar") {{ v, ⌜ v = (#globalVar) ⌝ }}) ∗
  "HglobalVar" ∷ globalVar ↦[uint64T] #v ∗

  "#HA" ∷ (□ WP pkg@#(str"A") {{ wp_A }}) ∗
  "#HB" ∷ (□ WP pkg@#(str"B") {{ wp_B }})
.

Lemma prove_is_bar :
  ⊢ WP bar #() {{ own_bar }}
.
Proof.
  iStartProof.
  iLöb as "IH".
  wp_rec.
  wp_apply wp_ref_zero; [done|].
  iIntros (?) "HglobalVar".
  wp_pures.
  wp_bind (MapInsert MapEmpty _ _).
  wp_lam; wp_pures.
  wp_lam; wp_pures.
  wp_lam; wp_pures.
  iModIntro.
  iFrame.
  iSplitL.
  { iModIntro. wp_lam; wp_pures. iPureIntro. done. }
  iSplitL.
  {
    iModIntro.
    do 3 (wp_lam; wp_pures).
    iModIntro.
    unfold wp_A.
    wp_rec.
Abort.

Lemma wp_test2:
  {{{ True }}}
    test2 #()
  {{{ RET #(LitInt (word.mul (U64 37) (U64 37))); True }}}.
Proof.
  iIntros (?) "Hpre HΦ".
  wp_lam.
  wp_apply wp_ref_zero.
  { done. }
  iIntros (x) "Hx".
  wp_pures.
  wp_store.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.

  wp_load.
  wp_load.
  wp_store.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.

  wp_load.
  wp_pures.
  wp_load.

  (* This should be abstracted away *)
  wp_lam; wp_pures; wp_lam; wp_pures.
  wp_lam; wp_pures; wp_lam; wp_pures.
  wp_lam; wp_pures; wp_lam; wp_pures.

  by iApply "HΦ".
Qed.

(* TODO: look at https://robbertkrebbers.nl/research/articles/iris_c.pdf *)
Axiom eval_exprs_unordered : list (expr) → expr.

Definition f : val :=
  λ: <>, #3.

Definition g : val :=
  λ: <>, #5.

Definition h : val :=
  λ: <>, #7.

Local Fixpoint glang_list_get_def (n:nat) : val :=
  λ: "v",
     match n with
     | 0%nat => Fst "v"
     | S n => glang_list_get_def n (Snd "v")
     end.
Local Definition glang_list_get_aux : seal (@glang_list_get_def). Proof. by eexists. Qed.
Definition glang_list_get := glang_list_get_aux.(unseal).
Local Definition glang_list_get_unseal :
  @glang_list_get = @glang_list_get_def := glang_list_get_aux.(seal_eq).
(* Global Arguments glang_list_get n. *)

(* y[f()] = g(z || h(), i()+x[j()], <-c) *)
Definition order_of_eval_test : val :=
  λ: <>,
  let: "0expr" := (eval_exprs_unordered [f #(); g #(); h#()]) in
  let: "e1" := (glang_list_get 0) ("0expr") in
  let: "e2" := (glang_list_get 1) ("0expr") in
  let: "e3" := (glang_list_get 2) ("0expr") in
  "e1" + "e2" + "e3"
.

Definition sp e P : val → iProp Σ :=
  λ v, (∀ Φ, (P -∗ WP e {{ Φ }}) -∗ Φ v)%I.

Axiom wp_eval_exprs_unordered3 :
  ∀ e1 e2 e3 Φ1 Φ2 Φ3 (Φ:_ → iProp Σ),
  (WP e1 {{ Φ1 }} ∗
  WP e2 {{ Φ2 }} ∗
  WP e3 {{ Φ3 }} ∗
  (∀ v1 v2 v3, Φ1 v1 ∗ Φ2 v2 ∗ Φ3 v3 -∗ (Φ (v1, (v2, (v3, #()))))%V)) -∗
  WP (eval_exprs_unordered [e1 ; e2 ; e3]) {{ Φ }}
.

(*
Axiom wp_eval_exprs_unordered3 :
  ∀ e2 e3 Φ2 Φ3 (Φ:_ → iProp Σ),
  WP e2 {{ Φ2 }} ∗
  WP e3 {{ Φ3 }} ∗
  (∀ v2 v3, Φ1 v1 ∗ Φ2 v2 ∗ Φ3 v3 -∗ (Φ (v1, (v2, (v3, #()))))%V)) -∗
  WP (eval_exprs_unordered [v1 ; e2 ; e3]) {{ Φ }}
. *)

(*
Axiom wp_sp_eval_exprs_unordered3 :
  ∀ e1 e2 e3 (Φ:_ → iProp Σ),
  (sp e1 Φ1∗
  sp e3 Φ2 ∗
  WP e3 {{ Φ3 }} ∗
  (∀ v  -∗ (Φ (v1, (v2, v3))%V))) -∗
  WP (eval_exprs_unordered [e1 ; e2 ; e3]) {{ Φ }}


* Translation looks weird compared to Go code
*
. *)

Lemma wp_value (v:val) :
  ⊢ WP of_val v {{ v', ⌜ v' = v ⌝ }}.
Proof. by iApply wp_value. Qed.

Lemma wp_order_of_eval_test :
  ∀ Φ,
  Φ #(U64 15) -∗
  WP order_of_eval_test #() {{ Φ }}
.
Proof.
  iIntros (?) "HΦ".
  wp_lam.
  wp_apply wp_eval_exprs_unordered3.
  iSplitR.
  (* FIXME: is there a setup where it is not necessary to have this explicit
     intermediate predicate? *)
  {
    unfold f.
    (* wp_pures without wp_finish *)
    lazymatch goal with
    | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
        let e := eval simpl in e in
          reshape_expr e ltac:(fun K e' =>
                                 wp_pure_filter e';
                                 eapply (tac_wp_pure_no_later _ _ _ K e')
                              ) || fail "wp_pure: cannot find redex pattern"
    | _ => fail "wp_pure: not a 'wp'"
    end.
    { apply _. }
    { done. }
    simpl.
    iApply wp_value.
  }
  iSplitR.
  { wp_lam. instantiate (1:=(λ v, ⌜v = #_⌝)%I). done. }
  iSplitR.
  { wp_lam. instantiate (1:=(λ v, ⌜v = #_⌝)%I). done. }
  iIntros "* (%&%&%)".
  subst.
  wp_pures.
  rewrite glang_list_get_unseal.
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
