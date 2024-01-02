From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From SkipList.atomic Require Import weakestpre.
From iris.heap_lang Require Export tactics derived_laws.
From iris.heap_lang Require Import notation.
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wp_expr_eval `{!heapGS_gen hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.
Lemma tac_twp_expr_eval `{!heapGS_gen hlc Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E [{ Φ }]) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_twp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_pure `{!heapGS_gen hlc Σ} Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "Hwp !> _" => //.
Qed.
Lemma tac_twp_pure `{!heapGS_gen hlc Σ} Δ s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP (fill K e2) @ s; E [{ Φ }]) →
  envs_entails Δ (WP (fill K e1) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ?? ->.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite -total_lifting.twp_pure_step //.
Qed.

Lemma tac_wp_pure_credit `{!heapGS_gen hlc Σ} Δ Δ' s E j K e1 e2 ϕ Φ :
  PureExec ϕ 1 e1 e2 →
  ϕ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  match envs_app false (Esnoc Enil j (£ 1)) Δ' with
  | Some Δ'' =>
     envs_entails Δ'' (WP fill K e2 @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ.
  pose proof @pure_exec_fill.
  rewrite -lifting.wp_pure_step_later; last done.
  rewrite into_laterN_env_sound /=. apply later_mono.
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  rewrite right_id. apply wand_intro_r. by rewrite wand_elim_l.
Qed.

Lemma tac_wp_value_nofupd `{!heapGS_gen hlc Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_value. Qed.
Lemma tac_twp_value_nofupd `{!heapGS_gen hlc Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. by apply twp_value. Qed.

Lemma tac_wp_value `{!heapGS_gen hlc Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_value_fupd. Qed.
Lemma tac_twp_value `{!heapGS_gen hlc Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. by rewrite twp_value_fupd. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) (λ _, twp _ ?E _ _)) =>
      eapply tac_twp_value_nofupd
  | |- envs_entails _ (twp ?s ?E (Val _) _) =>
      eapply tac_twp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_twp_pure _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" :=
  wp_pure _.

Tactic Notation "wp_pure" open_constr(efoc) "credit:" constr(H) :=
  iStartProof;
  let Htmp := iFresh in
  let finish _ :=
    pm_reduce;
    (iDestructHyp Htmp as H || fail 2 "wp_pure:" H "is not fresh");
    wp_finish
    in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure_credit _ _ _ _ Htmp K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |finish ()                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    fail "wp_pure: credit generation is not supported for a TWP"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" "credit:" constr(H) :=
  wp_pure _ credit: H.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{!heapGS_gen hlc Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.
Lemma tac_twp_bind `{!heapGS_gen hlc Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E [{ v, WP f (Val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: twp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_twp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; twp_bind_core K)
          | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{!heapGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.

Lemma tac_wp_allocN Δ Δ' s E j K v n Φ :
  (0 < n)%Z →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_allocN.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.
Lemma tac_twp_allocN Δ s E j K v n Φ :
  (0 < n)%Z →
  (∀ l,
    match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ with
    | Some Δ' =>
       envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }])
    | None => False
    end) →
  envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? HΔ.
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, twp_allocN.
  rewrite left_id. apply forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r.
Qed.

Lemma tac_wp_alloc Δ Δ' s E j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ' with
    | Some Δ'' =>
       envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? HΔ.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦ v)%I) right_id wand_elim_r.
Qed.
Lemma tac_twp_alloc Δ s E j K v Φ :
  (∀ l,
    match envs_app false (Esnoc Enil j (l ↦ v)) Δ with
    | Some Δ' =>
       envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }])
    | None => False
    end) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> HΔ.
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, twp_alloc.
  rewrite left_id. apply forall_intro=> l.
  specialize (HΔ l).
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ].
  rewrite envs_app_sound //; simpl.
  apply wand_intro_l. by rewrite (sep_elim_l (l ↦ v)%I) right_id wand_elim_r.
Qed.

Lemma tac_wp_free Δ Δ' s E i K l v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  (let Δ'' := envs_delete false i false Δ' in
   envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Free (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? Hlk Hfin.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_free.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  apply later_mono, sep_mono_r, wand_intro_r. rewrite right_id //.
Qed.
Lemma tac_twp_free Δ s E i K l v Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  (let Δ' := envs_delete false i false Δ in
   envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (Free (LitV l)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> Hlk Hfin.
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, twp_free.
  rewrite envs_lookup_split //; simpl.
  rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk).
  apply sep_mono_r, wand_intro_r. rewrite right_id //.
Qed.

Lemma tac_wp_load Δ Δ' s E i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_load Δ s E i K b l q v Φ :
  envs_lookup i Δ = Some (b, l ↦{q} v)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, twp_load.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  - iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  - iIntros "[$ He]". iIntros "Hl". iApply Hi. iApply "He". iFrame "Hl".
Qed.

Lemma tac_wp_store Δ Δ' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wand_entails, wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_store Δ s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (Store (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first by eapply wand_entails, twp_store.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_xchg Δ Δ' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ v) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Xchg (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wand_entails, wp_xchg.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_xchg Δ s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ v) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (Xchg (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first by eapply wand_entails, twp_xchg.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cmpxchg Δ Δ' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     v = v1 →
     envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})
  | None => False
  end →
  (v ≠ v1 →
   envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? Hsuc Hfail.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wand_entails, wp_cmpxchg_suc; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wand_entails, wp_cmpxchg_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.
Lemma tac_twp_cmpxchg Δ s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ with
  | Some Δ' =>
     v = v1 →
     envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }])
  | None => False
  end →
  (v ≠ v1 →
   envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ?? Hsuc Hfail.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -twp_bind. eapply wand_apply.
    { eapply wand_entails, twp_cmpxchg_suc; eauto. }
    rewrite /= {1}envs_simple_replace_sound //; simpl.
    apply sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -twp_bind. eapply wand_apply.
    { eapply wand_entails, twp_cmpxchg_fail; eauto. }
    rewrite /= {1}envs_lookup_split //; simpl.
    apply sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wp_cmpxchg_fail Δ Δ' s E i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?????.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_cmpxchg_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_fail Δ s E i K l q v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros. rewrite -twp_bind.
  eapply wand_apply; first by apply wand_entails, twp_cmpxchg_fail.
  (* [//] solves some evars and enables further simplification. *)
  rewrite envs_lookup_split /= // /=. by do 2 f_equiv.
Qed.

Lemma tac_wp_cmpxchg_suc Δ Δ' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  v = v1 → vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?????; subst.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply.
  { eapply wand_entails, wp_cmpxchg_suc; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_suc Δ s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  v = v1 → vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ with
  | Some Δ' =>
     envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=>????; subst.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply.
  { eapply wand_entails, twp_cmpxchg_suc; eauto. }
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_faa Δ Δ' s E i K l z1 z2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV z1)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (z1 + z2)))) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV z1) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, (wp_faa _ _ _ z1 z2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_faa Δ s E i K l z1 z2 Φ :
  envs_lookup i Δ = Some (false, l ↦ LitV z1)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (z1 + z2)))) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ LitV z1) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ??.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first by apply wand_entails, (twp_faa _ _ _ z1 z2).
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.
End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         twp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply lem; last iIntros pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.


Tactic Notation "wp_smart_apply" open_constr(lem) "as" constr(pat) :=
  wp_smart_apply lem; last iIntros pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_smart_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  wp_smart_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.


(** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise. The second one additionaly does some framing: it gets rid of [Hs] from
the context, reducing clutter. You get them all back in the continuation of the
atomic operation. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail);
  last iAuIntro.
Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  (* Convert "list of hypothesis" into specialization pattern. *)
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with
        [SGoal $ SpecGoal GSpatial false [] Hs false]); [iAccu|iApplyHyp H])
    ltac:(fun cont => fail);
  last iAuIntro.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|tc_solve
         |finish ()]
    in (process_single ()) || (process_array ())
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac
        |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_free" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_free: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free _ _ _ _ _ K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_free _ _ _ _ K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [solve_pointsto ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [tc_solve
    |solve_pointsto ()
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [solve_pointsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_pointsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_xchg" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_xchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_xchg _ _ _ _ _ K))
      |fail 1 "wp_xchg: cannot find 'Xchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_xchg _ _ _ _ K))
      |fail 1 "wp_xchg: cannot find 'Xchg' in" e];
    [solve_pointsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_xchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |try solve_vals_compare_safe
    |pm_reduce; intros H1; wp_finish
    |intros H2; wp_finish]
  | |- envs_entails _ (twp ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [solve_pointsto ()
    |try solve_vals_compare_safe
    |pm_reduce; intros H1; wp_finish
    |intros H2; wp_finish]
  | _ => fail "wp_cmpxchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_fail" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_fail: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_fail _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_fail _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [solve_pointsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_fail: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_suc" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_suc _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_pointsto ()
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_suc _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [solve_pointsto ()
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |pm_reduce; wp_finish]
  | _ => fail "wp_cmpxchg_suc: not a 'wp'"
  end.

Tactic Notation "wp_faa" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_faa: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_faa _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_faa _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [solve_pointsto ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_faa: not a 'wp'"
  end.
