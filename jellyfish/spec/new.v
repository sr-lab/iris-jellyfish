From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.


Local Open Scope Z.

Module NewSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.

    Theorem initLocks_spec (lvl: Z) (head: node_rep) (t: loc)
      (bot: bot_gname) (subs: list sub_gname) :
      {{{
        skip_list_equiv (lvl - 1) head ∅ 1 bot subs
        ∗
        t ↦□ rep_to_node tail
        ∗
        (node_next head +ₗ lvl) ↦∗ replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #t
        ∗
        (node_locks head +ₗ lvl) ↦∗ replicate (Z.to_nat (MAX_HEIGHT + 1 - lvl)) #()
        ∗
        ⌜ 1 ≤ lvl ≤ MAX_HEIGHT + 1 ⌝ 
        ∗
        ⌜ node_key head = INT_MIN ⌝ 
      }}}
        initLocks #(node_locks head) #lvl
      {{{ subs, RET #();
        skip_list_equiv MAX_HEIGHT head ∅ 1 bot subs
      }}}.
    Proof.
      iIntros (Φ) "(Hskip & #Ht & Hnext & Hlocks & Hlvl & %Hmin) HΦ".
      iRevert (lvl subs) "Hskip Hnext Hlocks Hlvl HΦ".
      iLöb as "IH".
      iIntros (lvl subs) "Hskip Hnext Hlocks %Hlvl HΦ".

      wp_lam. wp_let. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + iModIntro; iApply ("HΦ" $! subs).
        inversion Hcase; subst.
        by assert (MAX_HEIGHT + 1 - 1 = MAX_HEIGHT) as -> by lia.
      + assert (lvl ≠ MAX_HEIGHT + 1) as Hneq by congruence.
        destruct subs as [| top_sub bot_subs]; first by iExFalso.

        assert (Z.to_nat (MAX_HEIGHT + 1 - lvl) = S (Z.to_nat (MAX_HEIGHT - lvl))) as -> by lia.
        repeat rewrite replicate_S array_cons.
        iDestruct "Hlocks" as "(Hl & Hlocks)".
        iDestruct "Hnext" as "((Hnext' & Hnext'') & Hnext)".

        wp_apply (newlock_spec (in_lock lvl (Some top_sub) head) with "[Hnext'']").
        { iExists t; iFrame. }
        iIntros (l γ) "#Hlock".

        wp_store. wp_pures.
        iMod (mapsto_persist with "Hl") as "#Hl".

        iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
          as (γauth) "[Hown_auth _]"; 
          first by apply auth_both_valid.
        iMod (own_alloc (GSet node_key_range))
          as (γtoks) "Hown_toks"; first done.
        assert (node_key_range = node_key_range ∖ ∅) as -> by set_solver.

        set (sub := mk_sub_gname γauth γtoks).
        iMod (inv_alloc (levelN lvl) ⊤ (lazy_list_inv lvl head bot sub (Some top_sub)) 
          with "[Hnext' Hown_auth Hown_toks]") as "Hinv".
        {
          iNext; iExists ∅, ∅, nil. 
          assert (∅ = dom ∅) as <- by set_solver.
          iFrame. iSplit; first done. 
          iSplit.
          {
            assert (node_lt head tail); last (simpl; auto).
            rewrite /node_key in Hmin.
            rewrite /node_lt /node_key Hmin /=; apply HMIN_MAX.
          }
          iSplit; first rewrite /key_equiv //.
          iExists γ, l, t; iFrame "# ∗".
        }

        iApply ("IH" $! _ (sub :: top_sub :: bot_subs) with "[Hskip Hinv] [Hnext] [Hlocks] [%]").
        {
          assert (lvl + 1 - 1 = lvl) as -> by lia.
          iFrame. iPureIntro; lia.
        }
        {
          assert (MAX_HEIGHT + 1 - (lvl + 1) = MAX_HEIGHT - lvl) as -> by lia.
          rewrite -loc_add_assoc //.
        }
        {
          assert (MAX_HEIGHT + 1 - (lvl + 1) = MAX_HEIGHT - lvl) as -> by lia.
          rewrite -loc_add_assoc //.
        }
        { lia. }

        iNext; done.
    Qed.

    Theorem new_spec : 
      {{{ True }}}
        new #()
      {{{ p bot subs, RET #p; is_skip_list p ∅ 1 bot subs }}}.
    Proof.
      iIntros (Φ) "_ HΦ".
      pose proof HMAX_HEIGHT as Hmax.

      wp_lam. 
      wp_alloc t as "Ht"; iMod (mapsto_persist with "Ht") as "#Ht".
      wp_alloc next as "Hnext"; first lia. wp_let.
      wp_alloc locks as "Hlocks"; first lia. wp_let.

      assert (Z.to_nat (MAX_HEIGHT + 1) = S (Z.to_nat MAX_HEIGHT)) as -> by lia.
      rewrite replicate_S ?array_cons.
      iDestruct "Hnext" as "((Hn & Hn') & Hnext)".
      iDestruct "Hlocks" as "(Hlocks' & Hlocks)".

      wp_lam. wp_let. wp_pures.
      case_bool_decide as Hcase; first (inversion Hcase; lia).
      wp_if.

      set (head := (INT_MIN, dummy_null, next, @None loc, dummy_lock, locks)).
      wp_apply (newlock_spec (in_lock 0 None head) with "[Hn']").
      { 
        iExists t; rewrite loc_add_0; iFrame.
        iExists tail; iFrame "#"; by iLeft.
      }
      iIntros (l γ) "#Hlock".

      wp_pures; rewrite loc_add_0.
      wp_store; iMod (mapsto_persist with "Hlocks'") as "#Hl".
      wp_pures; assert (0 + 1 = 1) as -> by lia.

      iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
        as (γauth) "[Hown_auth _]"; 
        first by apply auth_both_valid.
      iMod (own_alloc (GSet node_key_range))
        as (γtoks) "Hown_toks"; 
        first done.
      iMod (own_alloc (●F (∅ : gmap Z (argmax Z)) ⋅ ◯F (∅: gmap Z (argmax Z))))
        as (γfrac) "[Hown_frac Hown_frac_frag]"; 
        first by apply auth_both_valid.
      assert (node_key_range = node_key_range ∖ dom (∅: gmap Z (argmax Z))) as -> by set_solver.

      set (sub := mk_sub_gname γauth γtoks).
      set (bot := mk_bot_gname γfrac).
      iMod (inv_alloc (levelN 0) ⊤ (lazy_list_inv 0 head bot sub None) 
        with "[Hn Hown_auth Hown_toks Hown_frac]") as "Hinv".
      {
        iNext; iExists ∅, ∅, nil. iFrame.
        iSplit; first done. iSplit.
        {
          assert (node_lt head tail); last (simpl; auto).
          rewrite /node_lt/node_key//=; apply HMIN_MAX.
        }
        iSplit; first rewrite /key_equiv //.

        iExists γ, l, t.
        repeat rewrite loc_add_0.
        iFrame "# ∗".
      }

      iAssert (skip_list_equiv 0 head ∅ 1 bot [sub]) 
        with "[Hinv Hown_frac_frag]" as "Hskip".
      { by iFrame. }

      assert (locks = node_locks head) as Hlocks by auto; rewrite Hlocks.
      wp_apply (initLocks_spec 1 head t with "[Hskip Hlocks Hnext]").
      {
        assert (MAX_HEIGHT + 1 - 1 = MAX_HEIGHT) as -> by lia.
        assert (1 - 1 = 0) as -> by lia.
        iFrame "# ∗". iPureIntro.
        by split; first lia.
      }
      iIntros (subs) "Hskip". wp_pures.
      rewrite (fold_rep_to_node head).

      wp_alloc p as "Hp"; iMod (mapsto_persist with "Hp") as "#Hp".
      iModIntro; iApply ("HΦ" $! p bot subs).
      iExists head. by iFrame "# ∗".
    Qed.

  End Proofs.
End NewSpec.