From stdpp Require Import coPset namespaces.
From iris.bi Require Export bi updates.
From iris.bi.lib Require Import fixpoint.
From iris.proofmode Require Import coq_tactics proofmode reduction.
From iris.prelude Require Import options.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import weakestpre.

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section post_definition.
  Context `{BiFUpd PROP} {TC : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (Ψ : TC → PROP) (* atomic postcondition *)
    (Q : PROP) (* keep Ψ condition *)
    (Φ : PROP) (* postcondition *)
  .

  (** atomic_post_acc as the "introduction form" of atomic postconditions: An 
      accessor that can return to [Q]. *)
  Definition atomic_post_acc Eo Ei Ψ Q Φ : PROP :=
    |={Eo, Ei}=> ∃.. z, Ψ z ∗ ((Ψ z ={Ei, Eo}=∗ Q) ∧ (Ψ z ={Ei, Eo}=∗ Φ)).

  Lemma atomic_post_acc_wand Eo Ei Ψ Q1 Q2 Φ1 Φ2 :
    ((Q1 -∗ Q2) ∧ (Φ1 -∗ Φ2)) -∗
    (atomic_post_acc Eo Ei Ψ Q1 Φ1 -∗ atomic_post_acc Eo Ei Ψ Q2 Φ2).
  Proof.
    iIntros "HQΦ Hpost". 
    iMod "Hpost" as (z) "[HΨ Hclose]". iModIntro. 
    iExists z. iFrame "HΨ". iSplitWith "Hclose".
    + iIntros "HΨ". iMod ("Hclose" with "HΨ") as "HQ".
      iModIntro. iApply "HQΦ". done.
    + iIntros "HΨ". iMod ("Hclose" with "HΨ") as "HΦ".
      iModIntro. iApply "HQΦ". done.
  Qed.

  Lemma atomic_post_acc_mask_weaken Eo1 Eo2 Ei Ψ Q Φ :
    Eo1 ⊆ Eo2 →
    atomic_post_acc Eo1 Ei Ψ Q Φ -∗ atomic_post_acc Eo2 Ei Ψ Q Φ.
  Proof.
    iIntros (HE) "Hpost".
    iMod (fupd_mask_subseteq Eo1) as "Hclose'"; first done.
    iMod "Hpost" as (z) "[HΨ Hclose]". iModIntro. 
    iExists z. iFrame "HΨ". iSplitWith "Hclose".
    + iIntros "HΨ". iMod ("Hclose" with "HΨ") as "HQ".
      iMod "Hclose'" as "_". iModIntro. done.
    + iIntros "HΨ". iMod ("Hclose" with "HΨ") as "HΦ".
      iMod "Hclose'" as "_". iModIntro. done.
  Qed.

  (** atomic_post as a fixed-point of the equation
   AP = atomic_post_acc Ψ AP Φ
  *)
  Context Eo Ei Ψ Φ.

  Definition atomic_post_pre (Θ : () → PROP) (_ : ()) : PROP :=
    atomic_post_acc Eo Ei Ψ (Θ ()) Φ.

  Local Instance atomic_post_pre_mono : BiMonoPred atomic_post_pre.
  Proof.
    constructor.
    - iIntros (Q1 Q2 ??) "#HQ12". iIntros ([]) "AP".
      iApply (atomic_post_acc_wand with "[HQ12] AP").
      iSplit; last auto. iApply "HQ12".
    - intros ??. solve_proper.
  Qed.

  Local Definition atomic_post_def :=
    bi_greatest_fixpoint atomic_post_pre ().

End post_definition.

(** Seal it *)
Local Definition atomic_post_aux : seal (@atomic_post_def).
Proof. by eexists. Qed.
Definition atomic_post := atomic_post_aux.(unseal).
Global Arguments atomic_post {PROP _ TC}.
Local Definition atomic_post_unseal :
  @atomic_post = _ := atomic_post_aux.(seal_eq).

Global Arguments atomic_post_acc {PROP _ TC} Eo Ei _ _ _ : simpl never.
Global Arguments atomic_post {PROP _ TC} Eo Ei _ _ : simpl never.

(** Notation: Atomic postconditions *)
Notation "'AP' '<<' ∃∃ z1 .. zn , Ψ '>>' @ Eo , Ei '<<' 'COMM' Φ '>>'" :=
  (atomic_post (TC:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
               Eo Ei
               (tele_app $ λ z1, .. (λ zn, Ψ%I) ..)
               Φ%I
  )
  (at level 20, Eo, Ei, Ψ, Φ at level 200, z1 binder, zn binder,
   format "'[hv   ' 'AP'  '<<'  '[' ∃∃  x1  ..  xn ,  '/' Ψ  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AP' '<<' Ψ '>>' @ Eo , Ei '<<' 'COMM' Φ '>>'" :=
  (atomic_post (TC:=TeleO) Eo Ei (tele_app Ψ%I) Φ%I
  )
  (at level 20, Eo, Ei, Ψ, Φ at level 200,
   format "'[hv   ' 'AP'  '<<'  '[' Ψ  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' COMM  Φ  ']' '>>' ']'") : bi_scope.

(** Lemmas about AP *)
Section post_lemmas.
  Context `{BiFUpd PROP}.

  Local Existing Instance atomic_post_pre_mono.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance atomic_post_acc_ne {TC : tele} Eo Ei n :
    Proper (
        pointwise_relation TC (dist n) ==>
        dist n ==>
        dist n ==>
        dist n
    ) (atomic_post_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance atomic_post_ne {TC : tele} Eo Ei n :
    Proper (
        pointwise_relation TC (dist n) ==>
        dist n ==>
        dist n
    ) (atomic_post (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic_post_unseal /atomic_post_def /atomic_post_pre. solve_proper.
  Qed.

  Lemma atomic_post_mask_weaken {TC : tele} Eo1 Eo2 Ei (Ψ : TC → PROP) Φ :
    Eo1 ⊆ Eo2 →
    atomic_post Eo1 Ei Ψ Φ -∗ atomic_post Eo2 Ei Ψ Φ.
  Proof.
    rewrite atomic_post_unseal {2}/atomic_post_def /=.
    iIntros (Heo) "HAP".
    iApply (greatest_fixpoint_coiter _ (λ _, atomic_post_def Eo1 Ei Ψ Φ)); last done.
    iIntros "!> *". rewrite {1}/atomic_post_def /= greatest_fixpoint_unfold.
    iApply atomic_post_acc_mask_weaken. done.
  Qed.

  Lemma atomic_post_wand {TC : tele} Eo Ei (Ψ : TC → PROP) Φ1 Φ2 :
    (Φ1 -∗ Φ2) -∗
    (atomic_post Eo Ei Ψ Φ1 -∗ atomic_post Eo Ei Ψ Φ2).
  Proof.
    rewrite atomic_post_unseal {2}/atomic_post_def /=.
    iIntros "HΦ Hpost".
    iApply (greatest_fixpoint_coiter _ (λ _, (Φ1 -∗ Φ2) ∗ atomic_post_def Eo Ei Ψ Φ1)%I); last iFrame.
    iIntros "!> * [HΦ Hpost]". rewrite {1}/atomic_post_def /= greatest_fixpoint_unfold.
    iApply (atomic_post_acc_wand with "[HΦ]"); last iFrame.
    iSplit; last done. iIntros; by iFrame.
  Qed.

  Lemma apst_unfold {TC : tele} Eo Ei (Ψ : TC → PROP) Φ :
    atomic_post Eo Ei Ψ Φ ⊣⊢
    atomic_post_acc Eo Ei Ψ (atomic_post Eo Ei Ψ Φ) Φ.
  Proof.
    rewrite atomic_post_unseal /atomic_post_def /=. apply: greatest_fixpoint_unfold.
  Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_mod_apost {TC : tele} φ Eo Ei E (Ψ : TC → PROP) Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic_post Eo Ei Ψ Φ)
              (∃.. z, Ψ z ∗ ((Ψ z ={Ei,E}=∗ atomic_post Eo Ei Ψ Φ) ∧ (Ψ z ={Ei,E}=∗ Φ)))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AP Hcont]".
    iDestruct (apst_unfold with "AP") as "AC".
    iMod (atomic_post_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  Local Lemma apst_intro {TC : tele} Eo Ei (Ψ : TC → PROP) Φ :
    Ei ⊆ Eo →
    (∃.. z, Ψ z ∗ (Ψ z -∗ Φ)) -∗
    atomic_post Eo Ei Ψ Φ.
  Proof.
    iIntros (HE) "(%z & HΨ & HΦ)".
    rewrite atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (λ _, (Ψ z ∗ (Ψ z -∗ Φ))%I)); last iFrame.
    iIntros "!> * [HΨ HΦ]". iApply (atomic_post_acc_wand with "[HΦ]").
    + iSplit; first iIntros "?"; by iFrame.
    + iApply fupd_mask_intro; first done.
      iIntros "Hclose". iExists z. iFrame "HΨ". 
      iSplit; iIntros "HΨ"; iMod "Hclose" as "_"; iModIntro; iFrame.
  Qed.

  Lemma apst_apst_sup {TC TC' : tele} E1 E1' E2 E3
        (Ψ : TC → PROP) (Φ : PROP)
        (Ψ' : TC' → PROP) (Φ' : PROP) 
        (R : PROP):
    E1' ⊆ E1 → E3 ⊆ E2 →
    R -∗
    □ (∀.. z, R ∗ Ψ z -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ R ∗ Ψ z))) -∗
    atomic_post E1' E2 Ψ Φ -∗
    (R ∗ atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ') -∗
    atomic_post E1 E3 Ψ' Φ'.
  Proof.
    iIntros (??) "HR #HRΨΨ' AP Hstep".
    rewrite {3} atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (λ _, (R ∗ atomic_post E1' E2 Ψ Φ ∗
      (R ∗ atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ')
    )%I)); last iFrame.
    iIntros "!> * [HR [AP Hstep]]".
    iMod (atomic_post_mask_weaken with "AP") as (z) "[HΨ [Hclose _]]"; first done.
    iApply fupd_mask_intro; first done. iIntros "Hclose'".
    iDestruct ("HRΨΨ'" with "[$]") as (z') "[HΨ' HRΨ]".
    iExists z'. iFrame "HΨ'".
    iSplit; iIntros "HΨ'"; iMod "Hclose'" as "_";
      iDestruct ("HRΨ" with "HΨ'") as "[HR HΨ]";
      iMod ("Hclose" with "HΨ") as "HΦ".
    + iModIntro. iFrame.
    + iApply "Hstep". iFrame. 
  Qed.

  Lemma apst_apst_sub {TC TC' : tele} E1 E1' E2 E3
        (Ψ : TC → PROP) (Φ : PROP)
        (Ψ' : TC' → PROP) (Φ' : PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    □ (∀.. z, Ψ z -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ Ψ z))) -∗
    atomic_post E1' E2 Ψ Φ -∗
    (atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ') -∗
    atomic_post E1 E3 Ψ' Φ'.
  Proof.
    iIntros (??) "#HΨΨ' AP Hstep".
    rewrite {3} atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (λ _, (atomic_post E1' E2 Ψ Φ ∗
      (atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ')
    )%I)); last iFrame.
    iIntros "!> * [AP Hstep]".
    iMod (atomic_post_mask_weaken with "AP") as (z) "[HΨ [Hclose _]]"; first done.
    iApply fupd_mask_intro; first done. iIntros "Hclose'".
    iDestruct ("HΨΨ'" with "HΨ") as (z') "[HΨ' HΨ]".
    iExists z'. iFrame "HΨ'".
    iSplit; iIntros "HΨ'"; iMod "Hclose'" as "_";
      iDestruct ("HΨ" with "HΨ'") as "HΨ"; 
      iMod ("Hclose" with "HΨ") as "HΦ".
    + iModIntro. iFrame.
    + by iApply "Hstep". 
  Qed.

  Lemma apst_apst_eq {TC : tele} E1 E1' E2 E3
        (Ψ : TC → PROP) Φ
        (Φ' : PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_post E1' E2 Ψ Φ -∗
    (atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ') -∗
    atomic_post E1 E3 Ψ Φ'.
  Proof.
    iIntros (??) "AP Hstep".
    iApply (apst_apst_sub with "[] AP"); try done.
    iIntros "!> * %z HΨ". iExists z. iFrame; iIntros; iFrame.
  Qed.

  Lemma atomic_post_commit {TC : tele} Eo Ei (Ψ : TC → PROP) Φ :
    atomic_post Eo Ei Ψ Φ ={Eo}=∗ Φ.
  Proof.
    iIntros "AP". iMod "AP" as (z) "[HΨ [_ HΦ]]".
    iMod ("HΦ" with "HΨ"). by iModIntro.
  Qed.

End post_lemmas.



Section definition.
  Context `{BiFUpd PROP} {TA TB TC : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic precondition *)
    (P : PROP) (* abortion condition *)
    (Ψ : TC → PROP) (* atomic postcondition *)
    (β : TA → TB → PROP)
    (Φ : TA → TB → PROP) (* postcondition *)
  .

  (** atomic_acc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  Definition atomic_acc Eo Ei α P Ψ β Φ : PROP :=
    |={Eo, Ei}=> ∃.. x, α x ∗ (
          (α x ={Ei, Eo}=∗ P) ∧ (* abort *)
          (∀.. y, β x y ={Ei, Eo}=∗ atomic_post Eo Ei Ψ (Φ x y)) (* commit *)
    ).

  Lemma atomic_acc_wand Eo Ei α P1 P2 Ψ β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀.. x y, Φ1 x y -∗ Φ2 x y)) -∗
    (atomic_acc Eo Ei α P1 Ψ β Φ1 -∗ atomic_acc Eo Ei α P2 Ψ β Φ2).
  Proof.
    iIntros "HPΦ AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HPΦ". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iMod ("Hclose" with "Hβ") as "HΦ1".
      iModIntro. iDestruct "HPΦ" as "[_ HΦ]".
      iApply (atomic_post_wand with "HΦ"). done.
  Qed.

  Lemma atomic_acc_mask_weaken Eo1 Eo2 Ei α P Ψ β Φ :
    Eo1 ⊆ Eo2 →
    atomic_acc Eo1 Ei α P Ψ β Φ -∗ atomic_acc Eo2 Ei α P Ψ β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod (fupd_mask_subseteq Eo1) as "Hclose'"; first done.
    iMod "Hstep" as (x) "[Hα Hclose]". iModIntro. iExists x.
    iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod ("Hclose" with "Hα") as "$". done.
    - iIntros (y) "Hβ". iMod ("Hclose" with "Hβ") as "HΦ".
      iMod "Hclose'" as "_". iModIntro.
      iApply atomic_post_mask_weaken; done.
  Qed.

  (** atomic_update as a fixed-point of the equation
   AU = atomic_acc α AU Ψ β Φ
  *)
  Context Eo Ei α Ψ β Φ.

  Definition atomic_update_pre (Θ : () → PROP) (_ : ()) : PROP :=
    atomic_acc Eo Ei α (Θ ()) Ψ β Φ.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
      iApply (atomic_acc_wand with "[HP12] AU").
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Local Definition atomic_update_def :=
    bi_greatest_fixpoint atomic_update_pre ().

End definition.

(** Seal it *)
Local Definition atomic_update_aux : seal (@atomic_update_def).
Proof. by eexists. Qed.
Definition atomic_update := atomic_update_aux.(unseal).
Global Arguments atomic_update {PROP _ TA TB TC}.
Local Definition atomic_update_unseal :
  @atomic_update = _ := atomic_update_aux.(seal_eq).

Global Arguments atomic_acc {PROP _ TA TB TC} Eo Ei _ _ _ _ _ : simpl never.
Global Arguments atomic_update {PROP _ TA TB TC} Eo Ei _ _ _ _ : simpl never.

(** Notation: Atomic updates *)
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
Notation "'AU' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β , 'POST' ∃∃ z1 .. zn , Ψ , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 (TC:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ z1, .. (λ zn, Ψ%I) ..)
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, Ψ, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv   ' 'AU'  '<<'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' POST  '[' ∃∃  z1  ..  zn ,  '/' Ψ  ']' ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AU' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'POST' ∃∃ z1 .. zn , Ψ , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 (TC:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
                 Eo Ei
                 (tele_app $ λ x1, .. (λ xn, α%I) ..)
                 (tele_app $ λ z1, .. (λ zn, Ψ%I) ..)
                 (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
                 (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, Ψ, β, Φ at level 200, x1 binder, xn binder, z1 binder, zn binder,
   format "'[hv   ' 'AU'  '<<'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' β ,  '/' POST  '[' ∃∃  z1  ..  zn ,  '/' Ψ  ']' ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AU' '<<' α '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β , 'POST' Ψ , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 (TC:=TeleO)
                 Eo Ei
                 (tele_app α%I)
                 (tele_app Ψ%I)
                 (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
                 (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, Ψ, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv   ' 'AU'  '<<'  '[' α  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' POST  Ψ ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AU' '<<' α '>>' @ Eo , Ei '<<' β , 'POST' Ψ , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleO) (TB:=TeleO) (TC:=TeleO)
                 Eo Ei
                 (tele_app α%I)
                 (tele_app Ψ%I)
                 (tele_app $ tele_app β%I)
                 (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, Ψ, β, Φ at level 200,
   format "'[hv   ' 'AU'  '<<'  '[' α  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' β ,  '/' POST  Ψ ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'AACC' '<<' ∃∃ x1 .. xn , α , 'ABORT' P '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β , 'POST' ∃∃ z1 .. zn , Ψ , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              (TC:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ z1, .. (λ zn, Ψ%I) ..)
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, β%I) .. )
                     ) .. )
              (tele_app $ λ x1, .. (λ xn,
                      tele_app (λ y1, .. (λ yn, Φ%I) .. )
                     ) .. )
  )
  (at level 20, Eo, Ei, α, P, Ψ, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv     ' 'AACC'  '<<'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' POST  '[' ∃∃  z1  ..  zn ,  '/' Ψ  ']' ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AACC' '<<' ∃∃ x1 .. xn , α , 'ABORT' P '>>' @ Eo , Ei '<<' β , 'POST' ∃∃ z1 .. zn , Ψ , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              (TC:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
              Eo Ei
              (tele_app $ λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app $ λ z1, .. (λ zn, Ψ%I) ..)
              (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
              (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, P, Ψ, β, Φ at level 200, x1 binder, xn binder, z1 binder, zn binder,
   format "'[hv     ' 'AACC'  '<<'  '[' ∃∃  x1  ..  xn ,  '/' α ,  '/' ABORT  P  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' β ,  '/' POST  '[' ∃∃  z1  ..  zn ,  '/' Ψ  ']' ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AACC' '<<' α , 'ABORT' P '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β , 'POST' Ψ , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              (TC:=TeleO)
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app Ψ%I)
              (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
              (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, P, Ψ, β, Φ at level 200, y1 binder, yn binder,
   format "'[hv     ' 'AACC'  '<<'  '[' α ,  '/' ABORT  P  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' POST  Ψ ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

Notation "'AACC' '<<' α , 'ABORT' P '>>' @ Eo , Ei '<<' β , 'POST' Ψ , 'COMM' Φ '>>'" :=
  (atomic_acc (TA:=TeleO)
              (TB:=TeleO)
              (TC:=TeleO)
              Eo Ei
              (tele_app α%I)
              P%I
              (tele_app Ψ%I)
              (tele_app $ tele_app β%I)
              (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, P, Ψ, β, Φ at level 200,
   format "'[hv     ' 'AACC'  '<<'  '[' α ,  '/' ABORT  P  ']' '>>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<<'  '[' β ,  '/' POST  Ψ ,  '/' COMM  Φ  ']' '>>' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  Context `{BiFUpd PROP}.

  Local Existing Instance atomic_update_pre_mono.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance atomic_acc_ne {TA TB TC : tele} Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        dist n ==>
        pointwise_relation TC (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance atomic_update_ne {TA TB TC : tele} Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TC (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic_update_unseal /atomic_update_def /atomic_update_pre. solve_proper.
  Qed.

  Lemma atomic_update_mask_weaken {TA TB TC : tele} Eo1 Eo2 Ei 
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    Eo1 ⊆ Eo2 →
    atomic_update Eo1 Ei α Ψ β Φ -∗ atomic_update Eo2 Ei α Ψ β Φ.
  Proof.
    rewrite atomic_update_unseal {2}/atomic_update_def /=.
    iIntros (Heo) "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, atomic_update_def Eo1 Ei α Ψ β Φ)); last done.
    iIntros "!> *". rewrite {1}/atomic_update_def /= greatest_fixpoint_unfold.
    iApply atomic_acc_mask_weaken. done.
  Qed.

  Lemma atomic_update_wand {TA TB TC : tele} Eo Ei 
    (α : TA → PROP) (Ψ : TC → PROP) (β Φ1 Φ2 : TA → TB → PROP) :
    (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    (atomic_update Eo Ei α Ψ β Φ1 -∗ atomic_update Eo Ei α Ψ β Φ2).
  Proof.
    rewrite atomic_update_unseal {2}/atomic_update_def /=.
    iIntros "HΦ Hupd".
    iApply (greatest_fixpoint_coiter _ (λ _, (∀.. x y, Φ1 x y -∗ Φ2 x y) ∗ 
      atomic_update_def Eo Ei α Ψ β Φ1
    )%I); last iFrame.
    iIntros "!> * [HΦ Hupd]". rewrite {1}/atomic_update_def /= greatest_fixpoint_unfold.
    iApply (atomic_acc_wand with "[HΦ]"); last iFrame.
    iSplit; last done. iIntros; by iFrame.
  Qed.

  Local Lemma aupd_unfold {TA TB TC : tele} Eo Ei 
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    atomic_update Eo Ei α Ψ β Φ ⊣⊢
    atomic_acc Eo Ei α (atomic_update Eo Ei α Ψ β Φ) Ψ β Φ.
  Proof.
    rewrite atomic_update_unseal /atomic_update_def /=. apply: greatest_fixpoint_unfold.
  Qed.

  (** The elimination form: an atomic accessor *)
  Lemma aupd_aacc {TA TB TC : tele} Eo Ei
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    atomic_update Eo Ei α Ψ β Φ ⊢
    atomic_acc Eo Ei α (atomic_update Eo Ei α Ψ β Φ) Ψ β Φ.
  Proof using Type*. by rewrite {1}aupd_unfold. Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_mod_aupd {TA TB TC : tele} φ Eo Ei E 
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP) Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic_update Eo Ei α Ψ β Φ)
              (∃.. x, α x ∗
                       (α x ={Ei,E}=∗ atomic_update Eo Ei α Ψ β Φ) ∧
                       (∀.. y, β x y ={Ei,E}=∗ atomic_post E Ei Ψ (Φ x y)))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (aupd_aacc with "AU") as "AC".
    iMod (atomic_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  (** The introduction lemma for atomic_update. This should usually not be used
  directly; use the [iAuIntro] tactic instead. *)
  Local Lemma aupd_intro {TA TB TC : tele} Eo Ei
      (α : TA → PROP) P Q (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    Absorbing P → Persistent P →
    (P ∧ Q ⊢ atomic_acc Eo Ei α Q Ψ β Φ) →
    P ∧ Q ⊢ atomic_update Eo Ei α Ψ β Φ.
  Proof.
    rewrite atomic_update_unseal {1}/atomic_update_def /=.
    iIntros (?? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coiter _ (λ _, Q)); last done. iIntros "!>" ([]) "HQ".
    iApply HAU. iSplit; by iFrame.
  Qed.

  Lemma aacc_intro {TA TB TC : tele} Eo Ei
      (α : TA → PROP) P (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    Ei ⊆ Eo → ⊢ (∀.. x, α x -∗ (
      (α x ={Eo}=∗ P) ∧ 
      (∀.. y, β x y ={Eo}=∗ ∃.. z, Ψ z ∗ (Ψ z -∗ Φ x y))
    ) -∗
    atomic_acc Eo Ei α P Ψ β Φ).
  Proof.
    iIntros (? x) "Hα Hclose".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod "Hclose'" as "_". iMod ("Hclose" with "Hβ"). 
      iModIntro. by iApply apst_intro.
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic accessor. *)
  Global Instance elim_acc_aacc {TA TB TC : tele} {X} E1 E2 Ei
      (α' β' : X → PROP) γ' 
      (α : TA → PROP) Pas (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (atomic_acc E1 Ei α Pas Ψ β Φ)
            (λ x', 
              atomic_acc E2 Ei α (β' x' ∗ (γ' x' -∗? Pas))%I Ψ β
              (λ.. x y, β' x' ∗ (γ' x' -∗? atomic_post E1 Ei Ψ (Φ x y)))
            )%I.
  Proof.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros (_) "Hinner Hacc".
    iMod "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iModIntro. iExists x. iFrame "Hα". iSplitWith "Hclose'".
    - iIntros "Hα".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'"). iModIntro.
      by iApply "HPas".
    - iIntros (y) "Hβ". 
      iMod ("Hclose'" with "Hβ") as "AP"; rewrite ->!tele_app_bind.
      iMod (atomic_post_commit with "AP") as "[Hβ' HAP]".
      iMod ("Hclose" with "Hβ'"). iModIntro.
      by iApply "HAP".
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  accessors can eliminate as well.  This is a forwarding instance needed because
  atomic_acc is becoming opaque. *)
  Global Instance elim_modal_acc {TA TB TC : tele} p q φ P P' Eo Ei 
      (α : TA → PROP) Pas (Ψ : TC → PROP) (β Φ : TA → TB → PROP) :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (atomic_acc Eo Ei α Pas Ψ β Φ)
              (atomic_acc Eo Ei α Pas Ψ β Φ).
  Proof. intros Helim. apply Helim. Qed.

  (** Lemmas for directly proving one atomic accessor in terms of another (or an
      atomic update).  These are only really useful when the atomic accessor you
      are trying to prove exactly corresponds to an atomic update/accessor you
      have as an assumption -- which is not very common. *)
  Lemma aacc_aacc {TA TB TC TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) P (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_acc E1' E2 α P Ψ β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (P ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        (α x ∗ (P ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y')))
        ∨ 
        (∃.. y, β x y ∗ (atomic_post E1 E2 Ψ (Φ x y) ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y')))
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (atomic_acc_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplitWith "Hclose'".
    - iIntros "Hα'". 
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". done.
    - iIntros (y') "Hβ'".
      iMod ("Hclose'" with "Hβ'") as "HAP". rewrite ->!tele_app_bind. 
      iMod "HAP" as (x'') "[HΨ' [_ HAP]]".
      iMod ("HAP" with "HΨ'") as "[[Hα HAP']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP". by iApply "HAP'".
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]". iDestruct "Hcont" as (y) "[Hβ HAP']".
        iMod ("Hclose" with "Hβ") as "HAP". by iApply "HAP'".
  Qed.

  Lemma aacc_aupd {TA TB TC TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α Ψ β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        (α x ∗ (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y')))
        ∨ 
        ∃.. y, β x y ∗ (atomic_post E1 E2 Ψ (Φ x y) ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y'))
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aacc _ E1' with "[Hupd] Hstep"); try done.
    iApply aupd_aacc; done.
  Qed.

  Lemma aacc_aupd_commit {TA TB TC TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α Ψ β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        ∃.. y, β x y ∗ (atomic_post E1 E2 Ψ (Φ x y) ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y'))
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); try done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iRight.
  Qed.

  Lemma aacc_aupd_abort {TA TB TC TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_update E1' E2 α Ψ β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        (α x ∗ (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ atomic_post E1 E3 Ψ' (Φ' x' y')))
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); try done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros (??) "?". rewrite ->!tele_app_bind. by iLeft.
  Qed.

  Lemma apst_aupd_sup {TA TB TC TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (Ψ' : TC' → PROP) (Φ' : PROP)
      (R : PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    R -∗
    □ (∀.. x, R ∗ α x -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ R ∗ α x))) -∗
    atomic_update E1' E2 α Ψ β Φ -∗
    (R ∗ atomic_update E1' E2 α Ψ β Φ ={E1}=∗ Φ') -∗
    atomic_post E1 E3 Ψ' Φ'.
  Proof.
    iIntros (??) "HR #HRαΨ' AU Hstep".
    rewrite atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (λ _, (R ∗ atomic_update E1' E2 α Ψ β Φ ∗
      (R ∗ atomic_update E1' E2 α Ψ β Φ ={E1}=∗ Φ')
    )%I)); last iFrame.
    iIntros "!> * [HR [AU Hstep]]".
    iMod (atomic_update_mask_weaken with "AU") as (x) "[Hα [Hclose _]]"; first done.
    iApply fupd_mask_intro; first done. iIntros "Hclose'".
    iDestruct ("HRαΨ'" with "[$]") as (z') "[HΨ' HRα]".
    iExists z'. iFrame "HΨ'". 
    iSplit; iIntros "HΨ'"; iMod "Hclose'" as "_";
      iDestruct ("HRα" with "HΨ'") as "[HR Hα]"; iMod ("Hclose" with "Hα");
      last iApply "Hstep"; by iFrame.
  Qed.

  Lemma apst_aupd_sub {TA TB TC TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (Ψ : TC → PROP) (β Φ : TA → TB → PROP)
      (Ψ' : TC' → PROP) (Φ' : PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    □ (∀.. x, α x -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ α x))) -∗
    atomic_update E1' E2 α Ψ β Φ -∗
    (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ Φ') -∗
    atomic_post E1 E3 Ψ' Φ'.
  Proof.
    iIntros (??) "#HαΨ' AU Hstep".
    rewrite atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (λ _, (atomic_update E1' E2 α Ψ β Φ ∗
      (atomic_update E1' E2 α Ψ β Φ ={E1}=∗ Φ')
    )%I)); last iFrame.
    iIntros "!> * [AU Hstep]".
    iMod (atomic_update_mask_weaken with "AU") as (x) "[Hα [Hclose _]]"; first done.
    iApply fupd_mask_intro; first done. iIntros "Hclose'".
    iDestruct ("HαΨ'" with "Hα") as (z') "[HΨ' Hα]".
    iExists z'. iFrame "HΨ'". 
    iSplit; iIntros "HΨ'"; iMod "Hclose'" as "_";
      iDestruct ("Hα" with "HΨ'") as "Hα"; iMod ("Hclose" with "Hα");
      last iApply "Hstep"; by iFrame.
  Qed.

  Lemma aacc_aupd_sup {TA TB TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP)
      (R : PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    R -∗
    □ (∀.. x, R ∗ α x -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ R ∗ α x))) -∗
    atomic_update E1' E2 α α β Φ -∗
    (∀.. x, R ∗ α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α α β Φ ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        (R ∗ α x ∗ (R ∗ atomic_update E1' E2 α α β Φ ={E1}=∗ Φ' x' y'))
        ∨ 
        ∃.. y, R ∗ β x y ∗ (R ∗ atomic_post E1 E2 α (Φ x y) ={E1}=∗ Φ' x' y')
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (??) "HR #HRαΨ' Hupd Hstep".
    iMod (atomic_update_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "[$]") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplitWith "Hclose'".
    - iIntros "Hα'". 
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". iFrame.
    - iIntros (y') "Hβ'".
      iMod ("Hclose'" with "Hβ'") as "HAP". rewrite ->!tele_app_bind. 
      iMod "HAP" as (z') "[HΨ' [_ HAP]]".
      iMod ("HAP" with "HΨ'") as "[[HR [Hα HAP']]|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HAP". iModIntro.
        iApply (apst_aupd_sup with "HR [] HAP"); try done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]". iDestruct "Hcont" as (y) "[HR [Hβ HAP']]".
        iMod ("Hclose" with "Hβ") as "HAP". iModIntro.
        iApply (apst_apst_sup with "HR [] HAP"); try done.
  Qed.

  Lemma aacc_aupd_sub {TA TB TA' TB' TC' : tele} E1 E1' E2 E3
      (α : TA → PROP) (β Φ : TA → TB → PROP)
      (α' : TA' → PROP) P' (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    □ (∀.. x, α x -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ α x))) -∗
    atomic_update E1' E2 α α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (atomic_update E1' E2 α α β Φ ={E1}=∗ P')) Ψ' β'
      (λ.. x' y', 
        (α x ∗ (atomic_update E1' E2 α α β Φ ={E1}=∗ Φ' x' y'))
        ∨ 
        ∃.. y, β x y ∗ (atomic_post E1 E2 α (Φ x y) ={E1}=∗ Φ' x' y')
      )) -∗
    atomic_acc E1 E3 α' P' Ψ' β' Φ'.
  Proof.
    iIntros (??) "#HαΨ' Hupd Hstep".
    iMod (atomic_update_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplitWith "Hclose'".
    - iIntros "Hα'". 
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". iFrame.
    - iIntros (y') "Hβ'".
      iMod ("Hclose'" with "Hβ'") as "HAP". rewrite ->!tele_app_bind. 
      iMod "HAP" as (z') "[HΨ' [_ HAP]]".
      iMod ("HAP" with "HΨ'") as "[[Hα HAP']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HAP". iModIntro.
        iApply (apst_aupd_sub with "[] HAP"); try done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]". iDestruct "Hcont" as (y) "[Hβ HAP']".
        iMod ("Hclose" with "Hβ") as "HAP". iModIntro.
        iApply (apst_apst_sub with "[] HAP"); try done.
  Qed.

  Lemma aacc_aupd_eq {TA TB TB' : tele} E1 E1' E2 E3
      (α : TA → PROP) (β Φ : TA → TB → PROP)
      P' (β' Φ' : TA → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_update E1' E2 α α β Φ -∗
    (∀.. x, α x -∗ atomic_acc E2 E3 α (α x ∗ (atomic_update E1' E2 α α β Φ ={E1}=∗ P')) α β'
      (λ.. x' y', 
        (α x ∗ (atomic_update E1' E2 α α β Φ ={E1}=∗ Φ' x' y'))
        ∨ 
        ∃.. y, β x y ∗ (atomic_post E1 E2 α (Φ x y) ={E1}=∗ Φ' x' y')
      )) -∗
    atomic_acc E1 E3 α P' α β' Φ'.
  Proof.
    iIntros (??) "AU Hstep".
    iApply (aacc_aupd_sub with "[] AU Hstep"); try done.
    iIntros "!> %x Hα". iExists x. iFrame; by iIntros.
  Qed.

  Lemma aacc_apst_sub {TC TA' TB' TC' : tele} E1 E1' E2 E3
      (Ψ : TC → PROP) Φ
      (α' : TA' → PROP) P (Ψ' : TC' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    □ (∀.. z, Ψ z -∗ ∃.. z', (Ψ' z' ∗ (Ψ' z' -∗ Ψ z))) -∗
    atomic_post E1' E2 Ψ Φ -∗
    (∀.. z, Ψ z -∗ atomic_acc E2 E3 α' (Ψ z ∗ (atomic_post E1' E2 Ψ Φ ={E1}=∗ P)) Ψ' β'
      (λ.. x' y', 
        (Ψ z ∗ (atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ' x' y'))
      )) -∗
    atomic_acc E1 E3 α' P Ψ' β' Φ'.
  Proof.
    iIntros (??) "#HαΨ' Hpst Hstep".
    iMod (atomic_post_mask_weaken with "Hpst") as (x) "[HΨ Hclose]"; first done.
    iMod ("Hstep" with "HΨ") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplitWith "Hclose'".
    - iIntros "Hα'". 
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". iFrame.
    - iIntros (y') "Hβ'".
      iMod ("Hclose'" with "Hβ'") as "HAP". rewrite ->!tele_app_bind. 
      iMod "HAP" as (z') "[HΨ' [_ HAP]]".
      iMod ("HAP" with "HΨ'") as "[HΨ HAP']".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "HΨ") as "HAP". iModIntro.
      iApply (apst_apst_sub with "[] HAP"); try done.
  Qed.

  Lemma aacc_apst_eq {TC TA' TB' TC' : tele} E1 E1' E2 E3
      (Ψ : TC → PROP) Φ
      (α' : TA' → PROP) P (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_post E1' E2 Ψ Φ -∗
    (∀.. z, Ψ z -∗ atomic_acc E2 E3 α' (Ψ z ∗ (atomic_post E1' E2 Ψ Φ ={E1}=∗ P)) Ψ β'
      (λ.. x' y', 
        (Ψ z ∗ (atomic_post E1' E2 Ψ Φ ={E1}=∗ Φ' x' y'))
      )) -∗
    atomic_acc E1 E3 α' P Ψ β' Φ'.
  Proof.
    iIntros (??) "Hpst Hstep".
    iApply (aacc_apst_sub with "[] Hpst Hstep"); try done.
    iIntros "!> %z HΨ". iExists z. iFrame; by iIntros.
  Qed.

End lemmas.

(** ProofMode support for atomic updates. *)
Section proof_mode.
  Context `{BiFUpd PROP} {TA TB TC : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP) (Ψ : TC → PROP) (P : PROP).

  Lemma tac_aupd_intro Γp Γs n α β Ψ Eo Ei Φ P :
    P = env_to_prop Γs →
    envs_entails (Envs Γp Γs n) (atomic_acc Eo Ei α P Ψ β Φ) →
    envs_entails (Envs Γp Γs n) (atomic_update Eo Ei α Ψ β Φ).
  Proof.
    intros ->. rewrite envs_entails_unseal of_envs_eq /atomic_acc /=.
    setoid_rewrite env_to_prop_sound =>HAU.
    rewrite assoc. apply: aupd_intro. by rewrite -assoc.
  Qed.
End proof_mode.

(** * Now the coq-level tactics *)

Tactic Notation "iAuIntro" :=
  match goal with
  | |- envs_entails (Envs ?Γp ?Γs _) (atomic_update _ _ _ _ _ ?Φ) =>
      notypeclasses refine (tac_aupd_intro Γp Γs _ _ _ _ _ _ Φ _ _ _); [
        (* P = ...: make the P pretty *) pm_reflexivity
      | (* the new proof mode goal *) ]
  end.

(** Tactic to apply [aacc_intro]. This only really works well when you have
[α ?] already and pass it as [iAaccIntro with "Hα"]. Doing
[rewrite /atomic_acc /=] is an entirely legitimate alternative. *)
Tactic Notation "iAaccIntro" "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |- envs_entails _ (@atomic_acc ?PROP ?H ?TA ?TB ?TC ?Eo ?Ei ?α ?P ?Ψ ?β ?Φ) =>
    iApply (@aacc_intro PROP H TA TB TC Eo Ei α P Ψ β Φ with sel);
    first try solve_ndisj; last iSplit
  | _ => fail "iAaccIntro: Goal is not an atomic accessor"
  end.

Lemma aupd_inv `{!irisGS_gen hlc Λ Σ} {TA TB : tele} E
  (α : TA → iProp Σ) (β Q Φ : TA → TB → iProp Σ) 
  I N :
  ↑N ⊆ E →
  inv N I -∗
  atomic_update (E ∖ ↑N) ∅ 
    α 
    α 
    β 
    (λ.. x y, Q x y -∗ Φ x y) -∗
  atomic_update E ∅ 
    (λ.. x, ▷I ∗ α x)
    (λ.. x, ▷I ∗ α x)
    (λ.. x y, ▷I ∗ β x y) 
    (λ.. x y, Q x y -∗ Φ x y).
Proof.
  iIntros (HN) "#Hinv AU".
  rewrite {2}atomic_update_unseal /atomic_update_def /=.
  iApply (greatest_fixpoint_coiter _ (
    λ _, (atomic_update (E ∖ ↑N) ∅ α α β (λ.. x y, Q x y -∗ Φ x y))%I
  )); last iFrame.
  iIntros "!> * AU". iInv N as "HI" "Hclose'".
  iMod "AU" as (x) "[Hα Hclose]".
  iModIntro. iExists x. rewrite ->!tele_app_bind.
  iFrame. iSplitWith "Hclose".
  + iIntros "[HI Hα]". iMod ("Hclose" with "Hα") as "AU".
    by iMod ("Hclose'" with "HI") as "_".
  + clear y; iIntros (y). rewrite ->!tele_app_bind.
    iIntros "[HI Hβ]". iMod ("Hclose" with "Hβ") as "AP".
    rewrite ->!tele_app_bind.
    iMod ("Hclose'" with "HI") as "_". iModIntro.

    rewrite {2}atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (
      λ _, (atomic_post (E ∖ ↑N) ∅ α (Q x y -∗ Φ x y))%I
    )); last iFrame.
    iIntros "!> * AP". iInv N as "HI" "Hclose'".
    iMod "AP" as (z) "[Hα Hclose]".
    iModIntro. iExists z. rewrite ->!tele_app_bind.
    iFrame. iSplitWith "Hclose"; iIntros "[HI Hα]";
      iMod ("Hclose" with "Hα") as "HΦ";
      iMod ("Hclose'" with "HI") as "_"; first done.
    iModIntro. iIntros "HQ". by iApply "HΦ".
Qed.

Lemma aupd_inv_timeless `{!irisGS_gen hlc Λ Σ} {TA TB : tele} E
  (α : TA → iProp Σ) (β Q Φ : TA → TB → iProp Σ) 
  I N `{!Timeless I} :
  ↑N ⊆ E →
  inv N I -∗
  atomic_update (E ∖ ↑N) ∅ 
    α 
    α 
    β 
    (λ.. x y, Q x y -∗ Φ x y) -∗
  atomic_update E ∅ 
    (λ.. x, I ∗ α x)
    (λ.. x, I ∗ α x)
    (λ.. x y, I ∗ β x y) 
    (λ.. x y, Q x y -∗ Φ x y).
Proof.
  iIntros (HN) "#Hinv AU".
  rewrite {2}atomic_update_unseal /atomic_update_def /=.
  iApply (greatest_fixpoint_coiter _ (
    λ _, (atomic_update (E ∖ ↑N) ∅ α α β (λ.. x y, Q x y -∗ Φ x y))%I
  )); last iFrame.
  iIntros "!> * AU". iInv N as ">HI" "Hclose'".
  iMod "AU" as (x) "[Hα Hclose]".
  iModIntro. iExists x. rewrite ->!tele_app_bind.
  iFrame. iSplitWith "Hclose".
  + iIntros "[HI Hα]". iMod ("Hclose" with "Hα") as "AU".
    by iMod ("Hclose'" with "HI") as "_".
  + clear y; iIntros (y). rewrite ->!tele_app_bind.
    iIntros "[HI Hβ]". iMod ("Hclose" with "Hβ") as "AP".
    rewrite ->!tele_app_bind.
    iMod ("Hclose'" with "HI") as "_". iModIntro.

    rewrite {2}atomic_post_unseal /atomic_post_def /=.
    iApply (greatest_fixpoint_coiter _ (
      λ _, (atomic_post (E ∖ ↑N) ∅ α (Q x y -∗ Φ x y))%I
    )); last iFrame.
    iIntros "!> * AP". iInv N as ">HI" "Hclose'".
    iMod "AP" as (z) "[Hα Hclose]".
    iModIntro. iExists z. rewrite ->!tele_app_bind.
    iFrame. iSplitWith "Hclose"; iIntros "[HI Hα]";
      iMod ("Hclose" with "Hα") as "HΦ";
      iMod ("Hclose'" with "HI") as "_"; first done.
    iModIntro. iIntros "HQ". by iApply "HΦ".
Qed.