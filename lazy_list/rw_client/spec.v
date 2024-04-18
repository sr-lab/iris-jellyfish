From iris.algebra Require Import frac_auth gset.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation.

From SkipList.atomic Require Import proofmode weakestpre.
From SkipList.lazy_list Require Import code inv.
From SkipList.lazy_list.spec Require Import spec.


Class rwG Σ := RWG { 
  rw_mutG :: inG Σ (frac_authR (gsetR Z));
  rw_agrG :: inG Σ (frac_authR (agreeR (gset Z)));
  rw_setG :: lazyG Σ
}.

Record rw_gname := mk_rw_gname {
  mut_gname: gname;
  agr_gname: gname
}.

Module RWSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module LASpec := LASpec Params.
  Export LASpec.

  Section invariant.
    Context `{!heapGS Σ, !rwG Σ} (N: namespace).

    Definition rw_lazyN := N .@ "rw_lazy".

    (* Public state for concurrent writes *)
    Definition mut_set (s: gset Z) (q: frac) (Γ: rw_gname) : iProp Σ := 
      own Γ.(mut_gname) (◯F{q} s).
    Lemma mut_set_sep (s: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      mut_set s (q1 + q2) Γ -∗ mut_set s q1 Γ ∗ mut_set s q2 Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; iFrame. Qed.
    Lemma mut_set_join (s1 s2: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      mut_set s1 q1 Γ ∗ mut_set s2 q2 Γ -∗ mut_set (s1 ⋅ s2) (q1 + q2) Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; by iCombine "Hmut1 Hmut2" as "Hmut". Qed.

    (* Public state for concurrent reads *)
    Definition const_set (s: gset Z) (q: frac) (Γ: rw_gname) : iProp Σ := 
      own Γ.(agr_gname) (◯F{q} (to_agree s)).
    Lemma const_set_sep (s: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      const_set s (q1 + q2) Γ -∗ const_set s q1 Γ ∗ const_set s q2 Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; iFrame. Qed.
    Lemma const_set_join (s1 s2: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      const_set s1 q1 Γ ∗ const_set s2 q2 Γ -∗ const_set (s1 ⋅ s2) (q1 + q2) Γ.
    Proof. 
      iIntros "(Hmut1 & Hmut2)"; iCombine "Hmut1 Hmut2" as "Hmut". 
      iDestruct (own_valid with "Hmut") as %[_ <-%to_agree_op_inv_L]%frac_auth_frag_valid.
      rewrite gset_op union_idemp_L agree_idemp //.
    Qed.

    (* Invariant concealing the abstract state of the full set *)
    Definition set_inv (p: loc) (Γl: lazy_gname) (Γ: rw_gname) : iProp Σ :=
      ∃ (s: gset Z),
        set p s Γl
        ∗
        own Γ.(mut_gname) (●F s)
        ∗
        own Γ.(agr_gname) (●F (to_agree s))
        ∗
        (own Γ.(mut_gname) (◯F s) ∨ own Γ.(agr_gname) (◯F (to_agree s))).
    Definition is_set (p: loc) (Γ: rw_gname) : iProp Σ :=
      ∃ (Γl: lazy_gname), inv rw_lazyN (set_inv p Γl Γ).
    Lemma rw_inv_alloc_mut (p: loc) (s: gset Z) (Γl: lazy_gname) :
      set p s Γl ={⊤}=∗ ∃ (Γ: rw_gname), is_set p Γ ∗ mut_set s 1 Γ.
    Proof.
      iIntros "Hset".
      iMod (own_alloc (●F s ⋅ ◯F s)) as (γmut) "[Hmut● Hmut◯]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F (to_agree s) ⋅ ◯F (to_agree s))) as (γagr) "[Hagr● Hagr◯]"; 
        first by apply auth_both_valid.
      set (Γ := mk_rw_gname γmut γagr).
      iMod (inv_alloc rw_lazyN ⊤ (set_inv p Γl Γ)
        with "[Hset Hmut● Hagr● Hagr◯]") as "#Hinv".
      { iNext; iExists s; iFrame. }
      iModIntro; iExists Γ; iFrame "# ∗"; by iExists Γl.
    Qed.
    Lemma rw_inv_alloc_const (p: loc) (s: gset Z) (Γl: lazy_gname) :
      set p s Γl ={⊤}=∗ ∃ (Γ: rw_gname), is_set p Γ ∗ const_set s 1 Γ.
    Proof.
      iIntros "Hset".
      iMod (own_alloc (●F s ⋅ ◯F s)) as (γmut) "[Hmut● Hmut◯]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F (to_agree s) ⋅ ◯F (to_agree s))) as (γagr) "[Hagr● Hagr◯]"; 
        first by apply auth_both_valid.
      set (Γ := mk_rw_gname γmut γagr).
      iMod (inv_alloc rw_lazyN ⊤ (set_inv p Γl Γ)
        with "[Hset Hmut● Hmut◯ Hagr●]") as "#Hinv".
      { iNext; iExists s; iFrame. }
      iModIntro; iExists Γ; iFrame "# ∗"; by iExists Γl.
    Qed.

    (* Helper lemmas for switching between concurrent writes and concurrent reads *)
    Lemma mut_to_const (p: loc) (s: gset Z) (Γ: rw_gname) :
      is_set p Γ -∗ mut_set s 1 Γ ={⊤}=∗ const_set s 1 Γ.
    Proof.
      rewrite /mut_set/const_set; iIntros "[%Γl #Hinv] Hmut◯".
      iInv "Hinv" as (s') ">(Hset & Hmut● & Hagr● & Hagr◯)".
      iDestruct (own_valid_2 with "Hmut● Hmut◯") as %->%frac_auth_agree_L.
      iDestruct "Hagr◯" as "[Hfalse|Hagr◯]".
      { by iDestruct (own_valid_2 with "Hmut◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iModIntro. iSplitR "Hagr◯"; last (iModIntro; iFrame).
      iNext; iExists s; iFrame.
    Qed.
    Lemma const_to_mut (p: loc) (s: gset Z) (Γ: rw_gname) :
      is_set p Γ -∗ const_set s 1 Γ ={⊤}=∗ mut_set s 1 Γ.
    Proof.
      rewrite /mut_set/const_set; iIntros "[%Γl #Hinv] Hagr◯".
      iInv "Hinv" as (s') ">(Hset & Hmut● & Hagr● & Hmut◯)".
      iDestruct (own_valid_2 with "Hagr● Hagr◯") as %Heq%frac_auth_agree.
      replace s' with s by rewrite -to_agree_op_valid_L Heq agree_idemp //.
      iDestruct "Hmut◯" as "[Hmut◯|Hfalse]"; last first.
      { by iDestruct (own_valid_2 with "Hagr◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iModIntro. iSplitR "Hmut◯"; last (iModIntro; iFrame).
      iNext; iExists s; iFrame.
    Qed.
  End invariant.

  Section proofs.
    Context `{!heapGS Σ, !rwG Σ} (N: namespace).
    Local Open Scope Z.

    Theorem read_spec (p: loc) (Γ: rw_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_set N p Γ ⊢ <<<
        ∀∀ (s: gset Z) (q: frac), const_set s q Γ |
        ∃∃ (b: bool), const_set s q Γ ∗ ⌜ if b then k ∈ s else k ∉ s ⌝;
        RET #b
      >>> @ ↑N
      {{{ emp }}} contains #p #k {{{ emp }}}.
    Proof.
      iIntros "[%Γl #Hinv]".
      iApply (atomic_wp_inv_timeless with "[] Hinv"); first solve_ndisj.
      iIntros "!> %Φ _ AU".

      awp_apply (contains_spec with "[$]"); first done.
      iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
      { 
        iIntros "!> %s %q [Hset ?]". iDestruct "Hset" as (s') "[? ?]". 
        iExists s'. iFrame. iIntros. iExists s'. iFrame.
      }
      iIntros (s q) "[Hset Hagr◯]".
      iDestruct "Hset" as (s') "(Hset & Hmut● & Hagr● & Hmut◯)".
      iAaccIntro with "Hset".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (b) "(Hset & Hif)".

      iDestruct (own_valid_2 with "Hagr● Hagr◯") as %Heq%frac_auth_included.
      rewrite Some_included_total to_agree_included leibniz_equiv_iff in Heq; 
        rewrite -Heq; clear Heq.

      iModIntro. iExists s. iFrame.
      iIntros "Hset". iRight. iExists b. iFrame.
      iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "_".
      iApply fupd_mask_mono; last by iApply "HΦ". solve_ndisj.
    Qed.

    Theorem write_spec (p: loc) (Γ: rw_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_set N p Γ ⊢ <<< 
        ∀∀ (s: gset Z) (q: frac), mut_set s q Γ |
        mut_set (s ⋅ {[ k ]}) q Γ;
        RET #()
      >>> @ ↑N
      {{{ emp }}} add #p #k {{{ emp }}}.
    Proof.
      iIntros "[%Γl #Hinv]".
      iApply (atomic_wp_inv_timeless with "[] Hinv"); first solve_ndisj.
      iIntros "!> %Φ _ AU".

      awp_apply (add_spec with "[$]"); first done.
      iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
      { 
        iIntros "!> %s %q [Hset ?]". iDestruct "Hset" as (s') "[? ?]". 
        iExists s'. iFrame. iIntros. iExists s'. iFrame.
      }
      iIntros (s q) "[Hset Hmut◯]".
      iDestruct "Hset" as (s') "(Hset & Hmut● & Hagr● & Hagr◯)".
      iAaccIntro with "Hset".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros "Hset".
      
      iMod (own_update_2 with "Hmut● Hmut◯") as "[Hmut● Hmut◯]".
      { by apply frac_auth_update, (op_local_update_discrete _ _ {[k]}). }
      do 2 rewrite (comm _ {[k]} _) gset_op.
      iDestruct "Hagr◯" as "[Hfalse|Hagr◯]".
      { by iDestruct (own_valid_2 with "Hmut◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iMod (own_update_2 with "Hagr● Hagr◯") as "[Hagr● Hagr◯]".
      { by apply (frac_auth_update_1 _ _ (to_agree (s' ∪ {[k]}))). }

      iModIntro. iExists (s' ∪ {[k]}). iFrame.
      iIntros "Hset". iRight. iFrame.
      iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "_".
      iApply fupd_mask_mono; last by iApply "HΦ". solve_ndisj.
    Qed.
  End proofs.
End RWSpec.