From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.

Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem array_inv (lvl: Z) (head: node_rep) (t: loc)
      (bot: bot_gname) (subs: list sub_gname) (γl: gname):
      skip_list_equiv lvl head ∅ 1 bot subs
      ∗
      is_lock γl (node_lock head) (is_array (node_next head) (MAX_HEIGHT + 1))
      ∗
      t ↦□ rep_to_node tail
      ∗
      (node_next head +ₗ lvl +ₗ 1) ↦∗{#1 / 2} replicate (Z.to_nat (MAX_HEIGHT - lvl)) #t 
      ∗
      ⌜ 0 ≤ lvl ≤ MAX_HEIGHT ⌝ 
      ∗
      ⌜ node_key head = INT_MIN ⌝ 
      ={⊤}=∗
        ∃ (subs: list sub_gname), 
          skip_list_equiv MAX_HEIGHT head ∅ 1 bot subs.
    Proof.
      remember (Z.to_nat (MAX_HEIGHT - lvl)) as diff eqn:Hdiff.
      iRevert (lvl subs Hdiff).
      iInduction diff as [|d] "IHdiff";
        iIntros (lvl subs Hdiff) "(Hlist & #Hlock & #Ht & Hnext & %Hmax & %Hmin)".

      + assert (lvl = MAX_HEIGHT) as -> by lia.
        iModIntro. iExists subs. iFrame.
      + destruct subs as [|γ subs]; first by iExFalso.

        rewrite replicate_S array_cons.
        iDestruct "Hnext" as "(Hnext' & Hnext)".

        iMod (own_alloc (● ∅ ⋅ ◯ ∅))
          as (γauth) "[Hown_auth _]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
          as (γtoks) "[Hown_toks _]"; 
          first by apply auth_both_valid.

        set (Γ := mk_sub_gname γauth γtoks).
        iMod (inv_alloc (levelN (lvl + 1)) ⊤ (lazy_list_inv (lvl + 1) head None Γ (Some γ)) 
          with "[Hnext' Hown_auth Hown_toks]") as "Hinv".
        {
          iNext; iExists ∅, nil. iFrame.
          rewrite /sub_list_inv set_map_empty.
          iFrame. iSplit; first done. iSplit. 
          {
            assert (node_lt head tail); last (simpl; auto).
            rewrite /node_key in Hmin.
            rewrite /node_lt /node_key Hmin /=; apply HMIN_MAX.
          }
          iExists γl, (MAX_HEIGHT + 1), t.
          rewrite -loc_add_assoc; iFrame "# ∗".
          iPureIntro; lia.
        }

        iApply ("IHdiff" $! (lvl + 1) (Γ :: γ :: subs) with "[%]").
        { lia. }

        iSplitL "Hinv Hlist".
        {
          rewrite /skip_list_equiv.
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          iFrame "# ∗". iPureIntro; lia.
        }

        rewrite -loc_add_assoc.
        iFrame "# ∗". iPureIntro.
        by split; first lia.
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ p bot subs, RET #p; is_skip_list p ∅ 1 bot subs }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      wp_lam. wp_alloc t as "Ht". wp_let.
      iMod (mapsto_persist with "Ht") as "#Ht".

      wp_alloc next as "Hnext".
      { pose proof HMAX_HEIGHT; lia. } 
      wp_let. iDestruct "Hnext" as "(Hnext' & Hnext)".

      wp_apply (newlock_spec (is_array next (MAX_HEIGHT + 1)) with "[Hnext']").
      { 
        iExists (replicate (Z.to_nat (MAX_HEIGHT + 1)) #t); iFrame.
        rewrite replicate_length //.
      }
      iIntros (l γl) "#Hlock".

      assert (Z.to_nat (MAX_HEIGHT + 1) = S (Z.to_nat MAX_HEIGHT)) as ->.
      { pose proof HMAX_HEIGHT; lia. } 
      rewrite replicate_S array_cons.
      iDestruct "Hnext" as "(Hnext' & Hnext)".

      wp_pures.
      set (head := (INT_MIN, dummy_null, next, @None loc, l, dummy_null)).
      rewrite (fold_rep_to_node head).

      iMod (own_alloc (● ∅ ⋅ ◯ ∅))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (● GSet ∅ ⋅ ◯ GSet ∅))
        as (γtoks) "[Hown_toks _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (●F ∅ ⋅ ◯F ∅))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.

      set (Γ := mk_sub_gname γauth γtoks).
      set (bot := mk_bot_gname γfrac).
      iMod (inv_alloc (levelN 0) ⊤ (lazy_list_inv 0 head (Some bot) Γ None) 
        with "[Hnext' Hown_auth Hown_toks Hown_frac]") as "Hinv".
      {
        iNext; iExists ∅, nil. iFrame.
        rewrite /sub_list_inv set_map_empty.
        iFrame. iSplit; first done. iSplit.
        {
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iExists γl, (MAX_HEIGHT + 1), t.
        rewrite loc_add_0; iFrame "# ∗". 
        iPureIntro; pose proof HMAX_HEIGHT; lia.
      }

      iAssert (skip_list_equiv 0 head ∅ 1 bot [Γ]) 
        with "[Hinv Hown_frac_frag]" as "Hskip".
      { by iFrame. }

      iPoseProof (array_inv 0 head t bot [Γ] γl with "[Hskip Hlock Hnext]") as "Hskip".
      {
        rewrite loc_add_0.
        assert (MAX_HEIGHT - 0 = MAX_HEIGHT) as -> by lia.
        iFrame "# ∗". iPureIntro.
        split; last done.
        pose proof HMAX_HEIGHT; lia.
      }
      iMod "Hskip" as (subs) "Hskip".

      wp_alloc p as "Hp"; iMod (mapsto_persist with "Hp") as "#Hp".
      iModIntro; iApply ("HΦ" $! _ bot subs).
      iExists head. by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.