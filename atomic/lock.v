From SkipList.atomic Require Import weakestpre proofmode.

From iris.heap_lang Require Import notation.
Import derived_laws_later.bi.


Definition newlock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.

Inductive state := Free | Locked.

Section proof.
  Context `{!heapGS Σ}.

  Definition acquired (lk: val) : iProp Σ :=
    ∃ (l: loc), ⌜ lk = #l ⌝ ∗ l ↦{#3 / 4} #true.

  Definition lock (lk: val) (st: state) (R: iProp Σ) : iProp Σ := 
    ∃ (l: loc), ⌜ lk = #l ⌝ ∗ 
    match st with
    | Free => l ↦ #false ∗ R
    | Locked => l ↦{#1 / 4} #true
    end.

  Global Instance lock_timeless lk st R `{!Timeless R} : Timeless (lock lk st R).
  Proof. destruct st; apply _. Qed.

  Lemma newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk, RET lk; lock lk Free R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". wp_lam. wp_alloc l as "Hl".
    iModIntro; iApply "HΦ". iExists l. by iFrame.
  Qed.

  Lemma try_acquire_spec (lk: val) (R : iProp Σ) :
    ⊢ <<< ∀∀ st, lock lk st R >>> try_acquire lk @ ∅
    <<< ∃∃ b, lock lk Locked R ∗ ⌜ if b is true then st = Free else st = Locked ⌝, RET #b >>>
    {{{ if b is true then acquired lk ∗ R else True }}}.
  Proof.
    iIntros (Φ) "AU"; rewrite difference_empty_L.
    wp_lam. wp_bind (CmpXchg _ _ _).
    iMod "AU" as ([]) "[Hlock [_ Hclose]]".
    + iDestruct "Hlock" as (l) "[-> [Hl HR]]". wp_cmpxchg_suc.
      rewrite -Qp.quarter_three_quarter; iDestruct "Hl" as "(Hl & Hl')".
      iDestruct ("Hclose" $! true with "[Hl]") as ">AP".
      { iSplit; last done. iExists l. by iFrame. }
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro; wp_pures. iApply "HΦ". 
      iFrame "HR". iExists l. by iFrame.
    + iDestruct "Hlock" as (l) "[-> Hl]". wp_cmpxchg_fail.
      iDestruct ("Hclose" $! false with "[Hl]") as ">AP".
      { iSplit; last done. iExists l. by iFrame. }
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro; wp_pures. by iApply "HΦ".
  Qed.

  Lemma acquire_spec (lk: val) (R : iProp Σ) :
    ⊢ <<< ∀∀ st, lock lk st R >>> acquire lk @ ∅ 
    <<< lock lk Locked R ∗ ⌜ st = Free ⌝, RET #() >>>
    {{{ acquired lk ∗ R }}}.
  Proof.
    iIntros (Φ) "AU"; rewrite difference_empty_L.
    iLöb as "IH". wp_lam.
    awp_apply try_acquire_spec.
    iApply (aacc_aupd_eq with "AU"); try done.
    iIntros (st) "Hlock"; iAaccIntro with "Hlock".
    { do 2 (iIntros; iModIntro; iFrame). }
    iIntros ([]) "[Hlock ->]".
    + iModIntro. iExists Locked. iFrame "Hlock". iIntros "Hlock". 
      iRight. iFrame. iSplit; first done. iIntros "AP".
      iMod (atomic_post_commit with "AP") as "HΦ".
      by iModIntro; iIntros; iModIntro; wp_pures; iApply "HΦ".
    + iModIntro. iExists Locked. iFrame "Hlock". iIntros "Hlock". 
      iLeft. iFrame. iIntros "AP". 
      by iModIntro; iIntros; iModIntro; wp_pures; iApply "IH".
  Qed.

  Lemma release_spec (lk: val) (R : iProp Σ) :
    acquired lk -∗ R -∗
    <<< ∀∀ st, lock lk st R >>> release lk @ ∅
    <<< lock lk Free R, RET #() >>>
    {{{ True }}}.
  Proof.
    iIntros "Hacq HR" (Φ) "AU"; rewrite difference_empty_L.
    iDestruct "Hacq" as (l) "[-> Hl]".
    wp_lam. iMod "AU" as ([]) "[Hlock [_ Hclose]]";
      iDestruct "Hlock" as (l') "[%Heq [Hl' HR']]"; replace l' with l by congruence.
    { iDestruct (mapsto_agree with "Hl Hl'") as %?; congruence. }
    iCombine "Hl Hl' HR'" as "Hl"; rewrite Qp.three_quarter_quarter.
    wp_store. iMod ("Hclose" with "[Hl HR]") as "AP".
    { iExists l. by iFrame. }
    iMod "AP" as (st) "[Hlock [_ HΦ]]". 
    iMod ("HΦ" with "Hlock") as "HΦ".
    by iApply "HΦ".
  Qed.
End proof.
