From stdpp Require Import namespaces.
From iris.bi.lib Require Export atomic.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants.

Section definition.
  Context {PROP : bi} `{!BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (E : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .
  
  Definition atomic_resource Eo Ei α Ψ :=  
    atomic_update Eo Ei α (λ (x : TA) (_ : TA), α x) (λ (_ : TA) (_ : TA), Ψ).
  Definition atomic_invariant Eo Ei α β Φ :=
    atomic_update Eo Ei α β (λ x y, atomic_resource Eo Ei α (Φ x y)).
  Definition updated_invariant Ψ α :=
    (∀.. (y : TB), Ψ y -∗ ∃.. x, α x ∗ (α x -∗ Ψ y))%I.

  Local Lemma ainv_aupd Eo Ei α β Φ :
    atomic_update Eo Ei α β (λ x y, atomic_resource Eo Ei α (Φ x y)) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof. by iIntros. Qed.

  Local Lemma ares_aupd Eo Ei α Ψ :
    atomic_update Eo Ei α (λ (x : TA) (_ : TA), α x) (λ (_ : TA) (_ : TA), Ψ) -∗
    atomic_resource Eo Ei α Ψ.
  Proof. by iIntros. Qed.
End definition.

(** Notation: Atomic invariants *)
Notation "'AI' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app $ λ x1, .. (λ xn,
                        tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                (tele_app $ λ x1, .. (λ xn,
                        tele_app (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
  format "'[hv   ' 'AI'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleO)
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
                (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
  format "'[hv   ' 'AI'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleO)
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                Eo Ei
                (tele_app α%I)
                (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
                (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
  format "'[hv   ' 'AI'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleO) (TB:=TeleO)
                Eo Ei
                (tele_app α%I)
                (tele_app $ tele_app β%I)
                (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
  format "'[hv   ' 'AI'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Notation: Atomic resources *)
Notation "'AR' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' Ψ '}>'" :=
  (atomic_resource (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app Ψ%I)
  )
  (at level 20, Eo, Ei, α, Ψ at level 200, x1 binder, xn binder,
  format "'[hv   ' 'AR'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '['  Ψ  ']' '}>' ']'") : bi_scope.

Notation "'AR' '<{' α '}>' @ Eo , Ei '<{' Ψ '}>'" :=
  (atomic_resource (TA:=TeleO)
                Eo Ei
                (tele_app α%I)
                (tele_app Ψ%I)
  )
  (at level 20, Eo, Ei, α, Ψ at level 200,
  format "'[hv   ' 'AR'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '['  Ψ  ']' '}>' ']'") : bi_scope.

(** Notation: Updated invariants *)
Notation "'UPD' '<{' ∀∀ y1 .. yn , β '}>' '<{' ∃∃ x1 .. xn , α '}>'" :=
  (updated_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                (tele_app $ λ y1, .. (λ yn, β%I) ..)
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
  )
  (at level 20, α, β at level 200, x1 binder, xn binder, y1 binder, yn binder,
  format "'[hv   ' 'UPD'  '<{'  '[' ∀∀  y1  ..  yn ,  '/' β  ']' '}>'  '/' '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>' ']'") : bi_scope.

Notation "'UPD' '<{' β '}>' '<{' ∃∃ x1 .. xn , α '}>'" :=
  (updated_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleO)
                (tele_app β%I)
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
  )
  (at level 20, α, β at level 200, x1 binder, xn binder,
  format "'[hv   ' 'UPD'  '<{'  '[' β  ']' '}>'  '/' '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>' ']'") : bi_scope.

Notation "'UPD' '<{' ∀∀ y1 .. yn , β '}>' '<{' α '}>'" :=
  (updated_invariant (TA:=TeleO)
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                (tele_app $ λ y1, .. (λ yn, β%I) ..)
                (tele_app α%I)
  )
  (at level 20, α, β at level 200, y1 binder, yn binder,
  format "'[hv   ' 'UPD'  '<{'  '[' ∀∀  y1  ..  yn ,  '/' β  ']' '}>'  '/' '<{'  '[' α  ']' '}>' ']'") : bi_scope.

Notation "'UPD' '<{' β '}>' '<{' α '}>'" :=
  (updated_invariant (TA:=TeleO) (TB:=TeleO)
                (tele_app β%I)
                (tele_app α%I)
  )
  (at level 20, α, β at level 200,
  format "'[hv   ' 'UPD'  '<{'  '[' β  ']' '}>'  '/' '<{'  '[' α  ']' '}>' ']'") : bi_scope.

Section properties.
  Context `{!irisGS_gen hlc Λ Σ} {TA TB : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (Φ : TA → TB → iProp) (Ψ : iProp).

  Lemma ainv_intro Eo Ei α β Φ :
    Ei ⊆ Eo →
    (∃.. x, α x ∗ updated_invariant (β x) α ∗ (∀.. y, (β x y -∗ (Φ x y)))) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof.
    iIntros (HE) "(%x & Hα & Hupd & HΦ)".
    iApply ainv_aupd. iAuIntro. iAaccIntro with "Hα".
    + iIntros "Hα". iModIntro. iFrame.
    + iIntros (y) "Hβ". iModIntro.
      iDestruct ("Hupd" with "Hβ") as (z) "[Hα Hβ]".
      iApply ares_aupd. iAuIntro. iAaccIntro with "Hα".
      - iIntros "Hα". iModIntro. iFrame.
      - iIntros (?) "Hα". iModIntro. iApply "HΦ". by iApply "Hβ".
  Qed.

  Lemma ainv_ainv_frame {TA' TB' : tele} E1 E1' E2 E3
        α β Φ R
        (α' : TA' → iProp) (β' Φ' : TA' → TB' → iProp) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_invariant E1' E2 α β Φ -∗
    R -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗ R -∗
        (α x ∗ (atomic_invariant E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        (∃.. y, β x y ∗ (atomic_resource E1' E2 α (Φ x y) ={E1}=∗ Φ' x' y')))
    )) -∗
    atomic_invariant E1 E3 α' β' Φ'.
  Proof.
    iIntros (HE HE') "AI HR #Hinv". iApply ainv_aupd. iAuIntro.
    iApply (aacc_aupd with "AI"); first done.
    iIntros (x) "Hα". iMod ("Hinv" with "Hα") as "[%x' [Hα' Hstep]]".
    iAaccIntro with "Hα'".
    + iIntros "Hα'". iDestruct ("Hstep") as "[Hα _]".
      iDestruct ("Hα" with "Hα'") as "Hα".
      iModIntro. iFrame. iIntros. iModIntro. iFrame.
    + iIntros (y') "Hβ'". iDestruct ("Hstep") as "[_ HΦ']".
      iMod ("HΦ'" with "Hβ'") as "HΦ'". iModIntro. rewrite ->!tele_app_bind.
      iDestruct ("HΦ'" with "HR") as "[[Hα HΦ'] | [%y [Hβ HΦ']]]".
      - iLeft. iFrame. iIntros "AI". iModIntro.
        unfold atomic_resource. iAuIntro.
        iApply (aacc_aupd with "AI"); first done.
        iIntros (z) "Hα". iMod ("Hinv" with "Hα") as "[%z' [Hα' [Hα _]]]".
        iAaccIntro with "Hα'".
        * iIntros "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
          iModIntro. iFrame. iIntros. iModIntro. iFrame.
        * iIntros (?) "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
          iModIntro. rewrite ->!tele_app_bind.
          iLeft. iFrame.
      - iRight. iExists y. iFrame. iIntros "AR". iModIntro.
        unfold atomic_resource. iAuIntro.
        iApply (aacc_aupd with "AR"); first done.
        iIntros (z) "Hα". iMod ("Hinv" with "Hα") as "[%z' [Hα' [Hα _]]]".
        iAaccIntro with "Hα'".
        * iIntros "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
          iModIntro. iFrame. iIntros. iModIntro. iFrame.
        * iIntros (?) "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
          iModIntro. rewrite ->!tele_app_bind. iFrame.
  Qed.

  Lemma ainv_ainv {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → iProp) (β' Φ' : TA' → TB' → iProp) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_invariant E1' E2 α β Φ -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗
        (α x ∗ (atomic_invariant E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        (∃.. y, β x y ∗ (atomic_resource E1' E2 α (Φ x y) ={E1}=∗ Φ' x' y')))
    )) -∗
    atomic_invariant E1 E3 α' β' Φ'.
  Proof.
    iIntros (HE HE') "AI #Hinv".
    iAssert emp%I as "R"; first done.
    iApply (ainv_ainv_frame with "AI R"); try done.
    iIntros "!>" (x) "Hα".
    iMod ("Hinv" with "Hα") as "[%x' [Hα' HΦ']]".
    iModIntro. iExists x'. iFrame.
    iSplit; first by iDestruct "HΦ'" as "[$ _]".
    iDestruct "HΦ'" as "[_ HΦ']". iIntros (y') "Hβ'".
    iMod ("HΦ'" with "Hβ'") as "HΦ'". iModIntro. by iIntros.
  Qed.

  Lemma ares_commit Eo Ei α Ψ :
    atomic_resource Eo Ei α Ψ ={Eo}=∗ Ψ.
  Proof.
    iIntros ">[%z [Hα [_ Hclose]]]".
    iMod ("Hclose" $! z with "Hα") as "HΦ".
    by iModIntro.
  Qed.

  Lemma ainv_ares_frame {TA' TB' : tele} E1 E1' E2 E3
        α Ψ R
        (α' : TA' → iProp) (β' Φ' : TA' → TB' → iProp) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_resource E1' E2 α Ψ -∗
    R -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗ R -∗
        α x ∗ (atomic_resource E1' E2 α Ψ ={E1}=∗ Φ' x' y'))
    )) -∗
    atomic_invariant E1 E3 α' β' Φ'.
  Proof.
    iIntros (HE HE') "AR HR #Hinv". iApply ainv_aupd. iAuIntro.
    iApply (aacc_aupd with "AR"); first done.
    iIntros (x) "Hα". iMod ("Hinv" with "Hα") as "[%x' [Hα' Hstep]]".
    iAaccIntro with "Hα'".
    + iIntros "Hα'". iDestruct ("Hstep") as "[Hα _]".
      iDestruct ("Hα" with "Hα'") as "Hα".
      iModIntro. iFrame. iIntros. iModIntro. iFrame.
    + iIntros (y') "Hβ'". iDestruct ("Hstep") as "[_ HΦ']".
      iMod ("HΦ'" with "Hβ'") as "HΦ'". iModIntro. rewrite ->!tele_app_bind.
      iDestruct ("HΦ'" with "HR") as "[Hα HΦ']".
      iLeft. iFrame. iIntros "AR". iModIntro.
      unfold atomic_resource. iAuIntro.
      iApply (aacc_aupd with "AR"); first done.
      iIntros (w) "Hα". iMod ("Hinv" with "Hα") as "[%w' [Hα' [Hα _]]]".
      iAaccIntro with "Hα'".
      * iIntros "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
        iModIntro. iFrame. iIntros. iModIntro. iFrame.
      * iIntros (?) "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
        iModIntro. rewrite ->!tele_app_bind.
        iLeft. iFrame.
  Qed.

  Lemma ainv_ares {TA' TB' : tele} E1 E1' E2 E3
        α Ψ
        (α' : TA' → iProp) (β' Φ' : TA' → TB' → iProp) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_resource E1' E2 α Ψ -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗
        α x ∗ (atomic_resource E1' E2 α Ψ ={E1}=∗ Φ' x' y'))
    )) -∗
    atomic_invariant E1 E3 α' β' Φ'.
  Proof.
    iIntros (HE HE') "AR #Hinv".
    iAssert emp%I as "R"; first done.
    iApply (ainv_ares_frame with "AR R"); try done.
    iIntros "!>" (x) "Hα".
    iMod ("Hinv" with "Hα") as "[%x' [Hα' HΦ']]".
    iModIntro. iExists x'. iFrame.
    iSplit; first by iDestruct "HΦ'" as "[$ _]".
    iDestruct "HΦ'" as "[_ HΦ']". iIntros (y') "Hβ'".
    iMod ("HΦ'" with "Hβ'") as "HΦ'". iModIntro. by iIntros.
  Qed.

  Lemma atomic_invariant_mask_weaken Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    atomic_invariant Eo1 Ei α β Φ -∗ atomic_invariant Eo2 Ei α β Φ.
  Proof.
    iIntros (HE) "AI".
    iApply (ainv_ainv with "AI"); try done.
    iIntros "!>" (x) "Hα". iModIntro. iExists x. iFrame.
    iSplit; first by iIntros. iIntros (y) "Hβ".
    iModIntro. iRight. iExists y. iFrame.
    iIntros ">[%z [Hα [_ Hclose]]]".
    by iApply ("Hclose" $! z).
  Qed.

  Lemma atomic_invariant_inv Eo Ei α β Φ N I :
    ↑N ⊆ Eo →
    atomic_invariant (Eo ∖ ↑N) Ei α β Φ -∗ inv N I -∗
    atomic_invariant Eo Ei (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) Φ.
  Proof.
    intros ?. iIntros "AI #Hinv".
    iApply ainv_aupd. iAuIntro. iInv N as "HI".
    iApply (aacc_aupd with "AI"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]".
      iModIntro. iRight. iExists y. iFrame. iIntros "AR".
      iModIntro. iApply ares_aupd. iAuIntro. iInv N as "HI".
      iApply (aacc_aupd with "AR"); first solve_ndisj.
      iIntros (z) "Hα". iAaccIntro with "[HI Hα]";
        rewrite ->!tele_app_bind; first by iFrame.
      * iIntros "[HI $]". iModIntro. iIntros "AR".
        iModIntro. iFrame.
      * iIntros (w) "[HI Hα]". iModIntro.
        rewrite ->!tele_app_bind. iRight.
        iExists w. iFrame. by iIntros.
  Qed.
End properties.
