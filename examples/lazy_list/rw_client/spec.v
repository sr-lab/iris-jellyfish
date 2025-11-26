From iris.algebra Require Import frac_auth gset.
From iris.base_logic.lib Require Import invariants.
From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.examples.lazy_list Require Import code inv.
From AtomicInvariant.examples.lazy_list.spec Require Import spec.


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

    (* Private state for concurrent writes *)
    Definition mut_set (s: gset Z) (q: frac) (Γ: rw_gname) : iProp Σ := 
      own Γ.(mut_gname) (◯F{q} s).
    Lemma mut_set_sep (s: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      mut_set s (q1 + q2) Γ -∗ mut_set s q1 Γ ∗ mut_set s q2 Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; iFrame. Qed.
    Lemma mut_set_join (s1 s2: gset Z) (q1 q2: frac) (Γ: rw_gname) :
      mut_set s1 q1 Γ ∗ mut_set s2 q2 Γ -∗ mut_set (s1 ⋅ s2) (q1 + q2) Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; by iCombine "Hmut1 Hmut2" as "Hmut". Qed.

    (* Private state for concurrent reads *)
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

    (* Invariant abstracting the public state of the full set *)
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

    Lemma read_updates_invariant (Γ: rw_gname) (k: Z) (s: gset Z) (q: frac) :
      ⊢ UPD <{ ∀∀ (b: bool), const_set s q Γ ∗ ⌜ if b then k ∈ s else k ∉ s ⌝ }>
        <{ ∃∃ (s : gset Z) (q : Qp), const_set s q Γ }>.
    Proof. iIntros ([]) "[? ?]"; iExists _, _; iFrame; by iIntros. Qed.
    Theorem read_spec (p: loc) (Γ: rw_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_set N p Γ ⊢ <<{ ∀∀ (s: gset Z) (q: frac), const_set s q Γ }>>
        contains #p #k @ ↑N
      <<{ ∃∃ (b: bool), const_set s q Γ ∗ ⌜ if b then k ∈ s else k ∉ s ⌝ | RET #b }>>.
    Proof.
      iIntros "[%Γl #Hinv]" (Φ) "AI".
      iDestruct (ainv_mask_weaken _ (⊤ ∖ ↑rw_lazyN N) with "AI")
        as "AI"; first solve_ndisj.
      iDestruct (atomic_invariant_inv with "AI Hinv") as "AI"; first done.
      iApply (contains_spec with "[AI]"); first done.

      iApply (ainv_ainv with "AI"); try done.
      iIntros "!> %s %q [>[%s' (Hset & Hmut● & Hagr● & Hmut◯)] Hagr◯] !>".
      iExists s'. iFrame "Hset". iSplit. { iIntros "Hset". iFrame. }
      iIntros (b) "[Hset Hif]".

      iDestruct (own_valid_2 with "Hagr● Hagr◯") as %Heq%frac_auth_included.
      rewrite Some_included_total to_agree_included leibniz_equiv_iff in Heq; 
        rewrite -Heq; clear Heq.
      iModIntro.
      
      iRight. iExists b. iFrame. iIntros "AR".
      rewrite difference_empty_L. iApply (ares_elim with "AR").
    Qed.

    Lemma write_updates_invariant (Γ: rw_gname) (k: Z) (s: gset Z) (q: frac) :
      ⊢ UPD <{ mut_set (s ⋅ {[ k ]}) q Γ }>
        <{ ∃∃ (s : gset Z) (q : Qp), mut_set s q Γ }>.
    Proof. iIntros ([]) "?"; iExists _, _; iFrame; by iIntros. Qed.
    Theorem write_spec (p: loc) (Γ: rw_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_set N p Γ ⊢ <<{ ∀∀ (s: gset Z) (q: frac), mut_set s q Γ }>>
        add #p #k @ ↑N
      <<{ mut_set (s ⋅ {[ k ]}) q Γ | RET #() }>>.
    Proof.
      iIntros "[%Γl #Hinv]" (Φ) "AI".
      iDestruct (ainv_mask_weaken _ (⊤ ∖ ↑rw_lazyN N) with "AI")
        as "AI"; first solve_ndisj.
      iDestruct (atomic_invariant_inv with "AI Hinv") as "AI"; first done.
      iApply (add_spec with "[AI]"); first done.

      iApply (ainv_ainv with "AI"); try done.
      iIntros "!> %s %q [>[%s' (Hset & Hmut● & Hagr● & Hagr◯)] Hmut◯] !>".
      iExists s'. iFrame "Hset". iSplit. { iIntros "Hset". iFrame. }
      iIntros "Hset". 

      iMod (own_update_2 with "Hmut● Hmut◯") as "[Hmut● Hmut◯]".
      { by apply frac_auth_update, (op_local_update_discrete _ _ {[k]}). }
      do 2 rewrite (comm _ {[k]} _) gset_op.
      iDestruct "Hagr◯" as "[Hfalse|Hagr◯]".
      { by iDestruct (own_valid_2 with "Hmut◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iMod (own_update_2 with "Hagr● Hagr◯") as "[Hagr● Hagr◯]".
      { by apply (frac_auth_update_1 _ _ (to_agree (s' ∪ {[k]}))). }
      iModIntro.

      iRight. iFrame. iIntros "AR".
      rewrite difference_empty_L. iApply (ares_elim with "AR").
    Qed.
  End proofs.
End RWSpec.