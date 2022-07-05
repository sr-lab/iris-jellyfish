From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.arrays Require Import code.
From SkipList.arrays.inv Require Import list_equiv lazy_inv skip_inv.


Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem array_inv (lvl: nat) (head: node_rep) (t: loc)
      (bot: bot_gname) (subs: list sub_gname) (γ: gname):
      skip_list_equiv lvl head ∅ 1 bot subs
      ∗
      is_lock γ (node_lock head) (node_inv (node_next head))
      ∗
      t ↦{#1 / exp2 (lvl + 1)} rep_to_node tail
      ∗
      (node_next head +ₗ lvl +ₗ 1) ↦∗{#1 / 2} replicate (MAX_HEIGHT - lvl) #t 
      ∗
      ⌜ 0 ≤ lvl ≤ MAX_HEIGHT ⌝ 
      ∗
      ⌜ node_key head = INT_MIN ⌝ 
      ={⊤}=∗
        ∃ (subs: list sub_gname), 
          skip_list_equiv MAX_HEIGHT head ∅ 1 bot subs.
    Proof.
      remember (MAX_HEIGHT - lvl) as diff eqn:Hdiff.
      iRevert (lvl subs Hdiff).
      iInduction diff as [|d] "IHdiff";
        iIntros (lvl subs Hdiff) "(Hlist & #Hlock & Ht & Hnext & %Hmax & %Hmin)".

      + assert (lvl = MAX_HEIGHT) as -> by lia.
        iModIntro. iExists subs. iFrame.
      + destruct subs as [| top_sub bot_subs]; first by iExFalso.

        rewrite replicate_S array_cons.
        iDestruct "Hnext" as "(Hnext' & Hnext)".
        iDestruct "Ht" as "(Ht & Ht')".

        iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
          as (γauth) "[Hown_auth _]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet node_key_range))
          as (γtoks) "Hown_toks"; first done.
        assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.

        set (sub := mk_sub_gname γauth γtoks).
        iMod (inv_alloc (levelN (lvl + 1)) ⊤ (lazy_list_inv (lvl + 1) head sub None (from_top_list top_sub)) 
          with "[Hnext' Ht' Hown_auth Hown_toks]") as "Hinv".
        {
          iNext; iExists ∅, ∅, nil. iFrame.
          iSplit; first done. iSplit.
          {
            assert (node_lt head tail); last (simpl; auto).
            rewrite /node_key in Hmin.
            rewrite /node_lt /node_key Hmin /=; apply HMIN_MAX.
          }
          iSplit; first rewrite /key_equiv //.
          iExists γ, t. 
          rewrite loc_add_assoc.
          assert (lvl + 1 + 1 = S (lvl + 1)) as -> by lia.
          assert ((lvl + 1)%Z = lvl + 1) as -> by lia.
          rewrite Qp_div_div comm_L //=.
          iFrame "# ∗".
        }

        iApply ("IHdiff" $! (lvl + 1) (sub :: top_sub :: bot_subs) with "[%]").
        { lia. }

        iSplitL "Hinv Hlist".
        {
          rewrite /skip_list_equiv.
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          iFrame "# ∗". iPureIntro; lia.
        }

        rewrite Qp_div_div comm_L //=.
        assert (lvl + 1 + 1 = S (lvl + 1)) as -> by lia.
        assert ((lvl + 1)%Z = lvl + 1) as <- by lia.
        rewrite -loc_add_assoc.
        iFrame "# ∗". iPureIntro.
        by split; first lia.
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ v bot subs, RET v; is_skip_list v ∅ 1 bot subs }}}.
    Proof.
      iIntros (Φ) "_ HΦ".

      wp_lam. wp_alloc t as "Ht". wp_let.
      wp_alloc next as "Hnext"; first lia. wp_let.
      assert (Z.to_nat (MAX_HEIGHT + 1) = S MAX_HEIGHT) as -> by lia.
      iDestruct "Hnext" as "(Hnext' & Hnext)".

      wp_apply (newlock_spec (node_inv next) with "[Hnext']").
      { iExists (replicate (S MAX_HEIGHT) #t); iFrame. }
      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".

      rewrite replicate_S array_cons.
      iDestruct "Hnext" as "(Hnext' & Hnext)".
      iDestruct "Ht" as "(Ht & Ht')".

      wp_pures.
      rewrite (fold_rep_to_node (INT_MIN, next, None, l)).
      set (head := (INT_MIN, next, None, l)).

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth Hown_auth_frag]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet node_key_range))
        as (γtoks) "Hown_toks"; 
        first done.
      iMod (own_alloc (●F (∅ : gset Z) ⋅ ◯F (∅: gset Z)))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.
      assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.

      set (sub := mk_sub_gname γauth γtoks).
      set (bot := mk_bot_gname γfrac).
      iMod (inv_alloc (levelN 0) ⊤ (lazy_list_inv 0 head sub (Some bot) from_bot_list) 
        with "[Hnext' Ht' Hown_auth Hown_toks Hown_frac]") as "Hinv".
      {
        iNext; iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit.
        {
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iSplit; first rewrite /key_equiv //.
        iExists γ, t.
        rewrite loc_add_0 /node_next /= Qp_mul_1_r.
        iFrame "# ∗".
      }

      iAssert (skip_list_equiv 0 head ∅ 1 bot [sub]) 
        with "[Hinv Hown_frac_frag]" as "Hskip".
      { by iFrame. }

      iPoseProof (array_inv 0 head t bot [sub] γ with "[Hskip Hlock Ht Hnext]") as "Hskip".
      {
        rewrite loc_add_assoc /node_next /= Qp_mul_1_r. 
        assert (0%nat + 1 = 1)%Z as -> by lia.
        assert (MAX_HEIGHT - 0 = MAX_HEIGHT) as -> by lia.
        iFrame "# ∗". iPureIntro.
        by split; first lia.
      }
      iMod "Hskip" as (subs) "Hskip".

      wp_alloc h as "Hh".
      iModIntro; iApply ("HΦ" $! _ bot subs).
      iExists h, head. by iFrame.
    Qed.

  End Proofs.
End NewSpec.