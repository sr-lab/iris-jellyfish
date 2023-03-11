From SkipList.atomic Require Import weakestpre proofmode.

From iris.heap_lang Require Import notation.
Import derived_laws_later.bi.


Definition newlock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.

Section proof.
  Context `{!heapGS Σ}.

  Definition locked (lk: val) : iProp Σ :=
    ∃ (l: loc), ⌜ lk = #l ⌝ ∗ l ↦{#3 / 4} #true.

  Definition lock (lk: val) (R: iProp Σ) : iProp Σ := 
    ∃ (l: loc) (b: bool), ⌜ lk = #l ⌝ ∗ l ↦{#1 / 4} #b ∗ 
      if b then True else l ↦{#3 / 4} #false ∗ R.

  Global Instance lock_timeless lk R `{!Timeless R} : Timeless (lock lk R).
  Proof.
    do 2 (apply exist_timeless; intros ?).
    do 2 (apply sep_timeless; first apply _).
    case_match; last apply sep_timeless; apply _.
  Qed.

  Lemma newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk, RET lk; lock lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". wp_lam. wp_alloc l as "Hl".
    rewrite -Qp.quarter_three_quarter; iDestruct "Hl" as "(Hl1 & Hl2)".
    iModIntro; iApply "HΦ". iExists l, false. by iFrame.
  Qed.

  Lemma try_acquire_spec (lk: val) (R : iProp Σ) :
    ⊢ <<< lock lk R >>> try_acquire lk @ ∅
    <<< ∃∃ b, lock lk R, RET #b >>>
    {{{ if b is true then locked lk ∗ R else True }}}.
  Proof.
    iIntros (Φ) "AU"; rewrite difference_empty_L.
    wp_lam. wp_bind (CmpXchg _ _ _).
    iMod "AU" as "[Hlock [_ Hclose]]".
    iDestruct "Hlock" as (l []) "(-> & Hl & Hif)".
    + wp_cmpxchg_fail.
      iDestruct ("Hclose" $! false with "[Hl Hif]") as ">AP".
      { iFrame. iExists l, true. by iFrame. }
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro; wp_pures. by iApply "HΦ".
    + iDestruct "Hif" as "(Hl' & HR)"; iCombine "Hl Hl'" as "Hl".
      rewrite Qp.quarter_three_quarter; wp_cmpxchg_suc.
      rewrite -Qp.quarter_three_quarter; iDestruct "Hl" as "(Hl & Hl')".
      iDestruct ("Hclose" $! true with "[Hl]") as ">AP".
      { iExists l, true. by iFrame. }
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro; wp_pures. iApply "HΦ". 
      iFrame "HR". iExists l. by iFrame.
  Qed.

  Lemma acquire_spec (lk: val) (R : iProp Σ) :
    ⊢ <<< lock lk R >>> acquire lk @ ∅ 
    <<< lock lk R, RET #() >>>
    {{{ locked lk ∗ R }}}.
  Proof.
    iIntros (Φ) "AU"; rewrite difference_empty_L.
    iLöb as "IH". wp_lam.
    awp_apply try_acquire_spec.
    iApply (aacc_aupd_eq with "AU"); try done.
    iIntros "Hlock"; iAaccIntro with "Hlock".
    { do 2 (iIntros; iModIntro; iFrame). }
    iIntros ([]) "Hlock".
    + iModIntro. iFrame "Hlock". iIntros "Hlock". 
      iRight. iFrame. iIntros "AP".
      iMod (atomic_post_commit with "AP") as "HΦ".
      by iModIntro; iIntros; iModIntro; wp_pures; iApply "HΦ".
    + iModIntro. iFrame "Hlock". iIntros "Hlock". 
      iLeft. iFrame. iIntros "AP". 
      by iModIntro; iIntros; iModIntro; wp_pures; iApply "IH".
  Qed.

  Lemma release_spec (lk: val) (R : iProp Σ) :
    locked lk -∗ R -∗
    <<< lock lk R >>> release lk @ ∅
    <<< lock lk R, RET #() >>>
    {{{ True }}}.
  Proof.
    iIntros "Hlocked HR" (Φ) "AU"; rewrite difference_empty_L.
    wp_lam. iMod "AU" as "[Hlock [_ Hclose]]".
    iDestruct "Hlock" as (l b) "(-> & Hl & _)".
    iDestruct "Hlocked" as (l') "(%Heq & Hl')". 
    symmetry in Heq; inversion Heq; subst.
    iDestruct (mapsto_agree with "Hl Hl'") as %<-.
    iCombine "Hl Hl'" as "Hl"; rewrite Qp.quarter_three_quarter.
    wp_store. iMod ("Hclose" with "[Hl HR]") as "AP".
    {
      rewrite -Qp.quarter_three_quarter; iDestruct "Hl" as "(HlL & HlR)".
      iExists l, false; by iFrame.
    }
    iMod "AP" as "[Hlock [_ HΦ]]". 
    iMod ("HΦ" with "Hlock") as "HΦ".
    by iApply "HΦ".
  Qed.
End proof.
