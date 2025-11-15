From stdpp Require Import namespaces.
From iris.bi.lib Require Export atomic.
From iris.proofmode Require Import proofmode.


Section definition.
  Context {PROP : bi} `{!BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (E : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .
  
  Definition atomic_resource Eo Ei α Φ := (λ x y,
    atomic_update Eo Ei α (λ (x : TA) (_ : TB), α x) (λ (_ : TA) (_ : TB), Φ x y))%I.
  Definition atomic_invariant Eo Ei α β Φ :=
    atomic_update Eo Ei α β (atomic_resource Eo Ei α Φ).

  Lemma ainv_aupd Eo Ei α β Φ :
    atomic_update Eo Ei α β (atomic_resource Eo Ei α Φ) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof. by iIntros. Qed.

  Lemma ares_aupd Eo Ei α Φ x y :
    atomic_update Eo Ei α (λ (x : TA) (_ : TB), α x) (λ (_ : TA) (_ : TB), Φ x y) -∗
    atomic_resource Eo Ei α Φ x y.
  Proof. by iIntros. Qed.
End definition.

Section properties.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β : TA → TB → PROP) (Ψ : PROP).

  Lemma ainv_intro Eo Ei α β Φ :
    Ei ⊆ Eo →
    (∃.. x, α x ∗ (∀.. y, β x y -∗ ∃.. z, α z ∗ (α z -∗ (Φ x y)))) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof.
    iIntros (HE) "(%x & Hα & HΦ)".
    iApply ainv_aupd. iAuIntro. iAaccIntro with "Hα".
    + iIntros "Hα". iModIntro. iFrame.
    + iIntros (y) "Hβ". iModIntro.
      iDestruct ("HΦ" with "Hβ") as (z) "[Hα HΦ]".
      iApply ares_aupd. iAuIntro. iAaccIntro with "Hα".
      - iIntros "Hα". iModIntro. iFrame.
      - iIntros (?) "Hα". iModIntro. by iApply "HΦ".
  Qed.

  Lemma ainv_ainv_frame {TA' TB' : tele} E1 E1' E2 E3
        α β Φ R
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_invariant E1' E2 α β Φ -∗
    R -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗ R -∗
        (α x ∗ (atomic_invariant E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        (∃.. y, β x y ∗ (atomic_resource E1' E2 α Φ x y ={E1}=∗ Φ' x' y')))
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
          iLeft. iIntros. by iApply "HΦ'".
  Qed.

  Lemma ainv_ainv {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_invariant E1' E2 α β Φ -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗
        (α x ∗ (atomic_invariant E1' E2 α β Φ ={E1}=∗ Φ' x' y')) ∨
        (∃.. y, β x y ∗ (atomic_resource E1' E2 α Φ x y ={E1}=∗ Φ' x' y')))
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

  Lemma ares_commit Eo Ei α Φ x (y : TB) :
    atomic_resource Eo Ei α Φ x y ={Eo}=∗ Φ x y.
  Proof.
    iIntros ">[%z [Hα [_ Hclose]]]".
    iMod ("Hclose" $! y with "Hα") as "HΦ".
    by iModIntro.
  Qed.

  Lemma ainv_ares_frame {TA' TB' : tele} E1 E1' E2 E3
        α Φ z (y : TB) R
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_resource E1' E2 α Φ z y -∗
    R -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗ R -∗
        α x ∗ (atomic_resource E1' E2 α Φ z y ={E1}=∗ Φ' x' y'))
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
      iDestruct ("HΦ'" with "HR") as "[Hα HΦ']".
      iLeft. iFrame. iIntros "AI". iModIntro.
      unfold atomic_resource. iAuIntro.
      iApply (aacc_aupd with "AI"); first done.
      iIntros (w) "Hα". iMod ("Hinv" with "Hα") as "[%w' [Hα' [Hα _]]]".
      iAaccIntro with "Hα'".
      * iIntros "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
        iModIntro. iFrame. iIntros. iModIntro. iFrame.
      * iIntros (?) "Hα'". iDestruct ("Hα" with "Hα'") as "Hα".
        iModIntro. rewrite ->!tele_app_bind.
        iLeft. iFrame.
  Qed.

  Lemma ainv_ares {TA' TB' : tele} E1 E1' E2 E3
        α Φ z (y : TB)
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 → E3 ⊆ E2 →
    atomic_resource E1' E2 α Φ z y -∗
    (□ ∀.. x, α x ={E2}=∗ ∃.. x', α' x' ∗ (
      (α' x' -∗ α x) ∧ (∀.. y', β' x' y' ={E2}=∗
        α x ∗ (atomic_resource E1' E2 α Φ z y ={E1}=∗ Φ' x' y'))
    )) -∗
    atomic_invariant E1 E3 α' β' Φ'.
  Proof.
    iIntros (HE HE') "AI #Hinv".
    iAssert emp%I as "R"; first done.
    iApply (ainv_ares_frame with "AI R"); try done.
    iIntros "!>" (x) "Hα".
    iMod ("Hinv" with "Hα") as "[%x' [Hα' HΦ']]".
    iModIntro. iExists x'. iFrame.
    iSplit; first by iDestruct "HΦ'" as "[$ _]".
    iDestruct "HΦ'" as "[_ HΦ']". iIntros (y') "Hβ'".
    iMod ("HΦ'" with "Hβ'") as "HΦ'". iModIntro. by iIntros.
  Qed.
End properties.
