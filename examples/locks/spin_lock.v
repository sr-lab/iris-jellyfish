From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import notation proofmode.


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

  Definition lock (lk: val) (st: state) : iProp Σ := 
    ∃ (l: loc), ⌜ lk = #l ⌝ ∗ 
    match st with
    | Free => l ↦ #false
    | Locked => l ↦{#1 / 4} #true
    end.

  Global Instance lock_timeless lk st : Timeless (lock lk st).
  Proof. destruct st; apply _. Qed.

  Lemma acquired_exclusive lk :
    acquired lk -∗ acquired lk -∗ False.
  Proof.
    iIntros "Hacq1 Hacq2".
    iDestruct "Hacq1" as (l1) "[%Heq1 Hl1]".
    replace 3%Qp with (2 + 1)%Qp by compute_done.
    rewrite Qp.div_add_distr.
    iDestruct "Hl1" as "(Hl1' & Hl1)".
    iDestruct "Hacq2" as (l2) "[%Heq2 Hl2]".
    replace l2 with l1 by congruence.
    iCombine "Hl1 Hl2" as "Hl".
    rewrite Qp.quarter_three_quarter.
    iDestruct (pointsto_ne with "Hl Hl1'") as %Hne; congruence.
  Qed.

  Lemma free_exclusive lk :
    acquired lk -∗ lock lk Free -∗ False.
  Proof.
    iIntros "Hacq Hlock".
    iDestruct "Hlock" as (l1) "[%Heq1 Hl1]".
    iDestruct "Hacq" as (l2) "[%Heq2 Hl2]".
    replace l2 with l1 by congruence.
    iDestruct (pointsto_ne with "Hl1 Hl2") as %Hne; congruence.
  Qed.

  Lemma newlock_spec :
    {{{ emp }}} newlock #() {{{ lk, RET lk; lock lk Free }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_alloc l as "Hl".
    iModIntro; iApply "HΦ". iExists l. by iFrame.
  Qed.

  Lemma try_acquire_spec (lk: val) :
    ⊢ <<{ ∀∀ st, lock lk st }>> try_acquire lk @ ∅
    <<{ ∃∃ b, lock lk Locked ∗ ⌜ if b is true then st = Free else st = Locked ⌝ | RET #b;
        if b is true then acquired lk else emp }>>.
  Proof.
    iIntros "" (Φ) "AI"; rewrite difference_empty_L.
    wp_lam. wp_bind (CmpXchg _ _ _).
    iMod "AI" as ([]) "[Hlock [_ Hclose]]".
    + iDestruct "Hlock" as (l) "[-> Hl]". wp_cmpxchg_suc.
      rewrite -Qp.quarter_three_quarter; iDestruct "Hl" as "(Hl & Hl')".
      iMod ("Hclose" $! true with "[Hl]") as "AR".
      { iSplit; last done. iExists l. by iFrame. }
      iMod (ares_commit with "AR") as "HΦ".
      iModIntro; wp_pures. iApply "HΦ".
      iExists l. by iFrame.
    + iDestruct "Hlock" as (l) "[-> Hl]". wp_cmpxchg_fail.
      iMod ("Hclose" $! false with "[Hl]") as "AR".
      { iSplit; last done. iExists l. by iFrame. }
      iMod (ares_commit with "AR") as "HΦ".
      iModIntro; wp_pures. by iApply "HΦ".
  Qed.

  Lemma acquire_spec (lk: val) :
    ⊢ <<{ ∀∀ st, lock lk st }>> acquire lk @ ∅
    <<{ lock lk Locked ∗ ⌜ st = Free ⌝ | RET #(); acquired lk }>>.
  Proof.
    iIntros "" (Φ) "AI". iLöb as "IH".
    wp_lam. wp_apply try_acquire_spec.
    iApply (ainv_ainv with "AI"); try done.
    iIntros "!>" (st) "Hlock !>". iExists st. iFrame.
    iSplit; first by iIntros. iIntros ([]) "[Hlock ->]".
    + iRight. iFrame. iModIntro. iSplit; first done.
      iIntros "AR !> Hacq". wp_pures.
      rewrite difference_empty_L; iMod (ares_commit with "AR") as "HΦ".
      iModIntro. by iApply "HΦ".
    + iLeft. iFrame. iIntros "!> AI".
      iIntros "!> _". wp_pures. by iApply "IH".
  Qed.

  Lemma release_spec (lk: val) :
    ⊢ acquired lk -∗ <<{ ∀∀ st, lock lk st }>> release lk @ ∅
    <<{ lock lk Free | RET #() }>>.
  Proof.
    iIntros "Hacq" (Φ) "AI".
    iDestruct "Hacq" as (l) "[-> Hl]".
    wp_lam. iMod "AI" as ([]) "[Hlock [_ Hclose]]";
      iDestruct "Hlock" as (l') "[%Heq Hl']"; replace l' with l by congruence.
    { iDestruct (pointsto_agree with "Hl Hl'") as %?; congruence. }
    iCombine "Hl Hl'" as "Hl"; rewrite Qp.three_quarter_quarter. wp_store.
    iMod ("Hclose" with "[Hl]") as "AR".
    { iExists l. by iFrame. }
    by rewrite difference_empty_L; iMod (ares_commit with "AR") as "HΦ".
  Qed.
End proof.
