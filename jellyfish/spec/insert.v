From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset gmap.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jellyfish.spec Require Import link.


Local Open Scope Z.

Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Link := LinkSpec Params.
  Export Link.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ}.

    Theorem update_spec (v ts: Z) (head curr: node_rep) 
      (Smap: gmap Z (argmax Z)) (q: frac)
      (sub: sub_gname) (bot: bot_gname) 
      (val: val_rep) :
      {{{
        is_bot_list 0 head Smap q bot sub
        ∗
        own (s_auth sub) (◯ {[ curr ]})
        ∗
        (node_val curr) ↦{#1 / 2} rep_to_val val
      }}}
        update (rep_to_node curr) #v #ts
      {{{ val', RET #();
        is_bot_list 0 head (Smap ⋅ {[ node_key curr := prodZ {[ v ]} ts ]}) q bot sub
        ∗
        (node_val curr) ↦{#1 / 2} rep_to_val val'
        ∗
        if decide (ts < val_ts val) then ⌜ val = val' ⌝  
                                    else ⌜ val_v val' = v ⌝
                                         ∗
                                         ⌜ val_ts val' = ts ⌝
                                         ∗
                                         (val_prev val') ↦□ rep_to_val val
      }}}.
    Proof.
      iIntros (Φ) "((Hown_frag & #Hinv) & #Hown_succ & Hval) HΦ".

      wp_lam. wp_pures. wp_lam. wp_pures.
      wp_load. wp_let. wp_lam. wp_pures.

      case_bool_decide as Hts; wp_if.
      + iInv (levelN 0) as (S' Smap' L) "(Hinv_sub & Hinv_bot)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
        iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".

        iAssert ⌜ In curr L ⌝%I with "[Hown_auth]" as %Hin.
        {
          iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite -elem_of_list_In Hperm elem_of_elements.
          iPureIntro; set_solver.
        }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (val' γ l s succ) "(_ & Hpt & _ & _ & _ & >Hnode & >%Hval & Himp)".
        iDestruct (mapsto_agree with "Hval Hnode") as %<-%rep_to_val_inj.
        destruct Hval as [vs [Hsome Hv]].

        assert (Smap ⋅ ∅ = Smap) as <- by rewrite right_id_L //.
        rewrite -(Qp_div_2 q) frac_auth_frag_op.
        iDestruct "Hown_frag" as "(Hown_frag & Hown_emp)".
        iMod (own_update_2 with "Hown_frac Hown_emp") as "[Hown_frac Hown_emp]".
        { 
          apply frac_auth_update. 
          apply (insert_alloc_local_update _ _ 
            (node_key curr) 
            (prodZ vs (val_ts val)) 
            (prodZ {[v]} ts ⋅ prodZ vs (val_ts val)) 
            (prodZ {[v]} ts)
          ); auto.
          apply arg_max_local_update.
        }

        rewrite arg_max_lt; last done.
        rewrite insert_id; last done.
        rewrite insert_singleton_op; last done.
        do 2 rewrite right_id_L.
        iCombine "Hown_frag Hown_emp" as "Hown_frag".
        rewrite Qp_div_2.

        iPoseProof ("Himp" $! vs val with "[Hpt Hnode]") as "Hlist".
        { iNext; by iFrame. }
        rewrite /opt_map /opt_insert insert_id //.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
        { iNext; iExists S', Smap', L; by iFrame "# ∗". }
        iModIntro; iApply ("HΦ" $! val).
        iFrame "# ∗".
        by destruct (decide (ts < val_ts val)).
      + wp_alloc v' as "Hval'"; wp_pures.
        iInv (levelN 0) as (S' Smap' L) "(Hinv_sub & Hinv_bot)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
        iDestruct "Hinv_bot" as "(>Hown_frac & >Hown_keys)".

        iAssert ⌜ In curr L ⌝%I with "[Hown_auth]" as %Hin.
        {
          iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite -elem_of_list_In Hperm elem_of_elements.
          iPureIntro; set_solver.
        }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (val' γ l s succ) "(_ & Hpt & _ & _ & _ & >Hnode & >%Hval & Himp)".
        iDestruct (mapsto_agree with "Hval Hnode") as %<-%rep_to_val_inj.
        destruct Hval as [vs [Hsome Hv]].

        assert (Smap ⋅ ∅ = Smap) as <- by rewrite right_id_L //.
        rewrite -(Qp_div_2 q) frac_auth_frag_op.
        iDestruct "Hown_frag" as "(Hown_frag & Hown_emp)".
        iMod (own_update_2 with "Hown_frac Hown_emp") as "[Hown_frac Hown_emp]".
        { 
          apply frac_auth_update. 
          apply (insert_alloc_local_update _ _ 
            (node_key curr) 
            (prodZ vs (val_ts val)) 
            (prodZ {[v]} ts ⋅ prodZ vs (val_ts val)) 
            (prodZ {[v]} ts)
          ); auto.
          apply arg_max_local_update.
        }

        rewrite (insert_singleton_op _ _ (prodZ {[v]} ts)); last done.
        do 2 rewrite right_id_L.
        iCombine "Hown_frag Hown_emp" as "Hown_frag".
        rewrite Qp_div_2.

        set (val' := (v, ts, v')).
        rewrite (fold_rep_to_val val').
        iCombine "Hval Hnode" as "Hval".
        wp_store.
        iDestruct "Hval" as "(Hval & Hnode)".
        iMod (mapsto_persist with "Hval'") as "#Hval'".

        assert (val_ts val = ts ∨ val_ts val < ts) as Hts_range by lia.
        clear Hts; destruct Hts_range as [->|Hlt].
        - rewrite arg_max_eq.
          iPoseProof ("Himp" $! ({[ v ]} ∪ vs) val' with "[Hpt Hnode]") as "Hlist".
          { iFrame; iPureIntro; by apply elem_of_union_l, elem_of_singleton. }

          assert (dom (<[node_key curr:=prodZ ({[v]} ∪ vs) ts]> Smap') = dom Smap') as Hdom.
          { apply dom_insert_lookup_L; by exists (prodZ vs (val_ts val)). }
          rewrite -Hdom; rewrite -Hdom in Hequiv.

          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
          { iNext; iExists S', (<[node_key curr:=prodZ ({[v]} ∪ vs) ts]> Smap'), L; by iFrame "# ∗". }
          iModIntro; iApply ("HΦ" $! val').
          iFrame "# ∗".
          destruct (decide (ts < ts)); first lia.
          by iFrame "#".
        - rewrite arg_max_op arg_max_comm -arg_max_op arg_max_lt; last done.
          iPoseProof ("Himp" $! {[ v ]} val' with "[Hpt Hnode]") as "Hlist".
          { iFrame; iPureIntro; by apply elem_of_singleton. }

          assert (dom (<[node_key curr:=prodZ {[v]} ts]> Smap') = dom Smap') as Hdom.
          { apply dom_insert_lookup_L; by exists (prodZ vs (val_ts val)). }
          rewrite -Hdom; rewrite -Hdom in Hequiv.

          iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac Hown_keys]") as "_".
          { iNext; iExists S', (<[node_key curr:=prodZ {[v]} ts]> Smap'), L; by iFrame "# ∗". }
          iModIntro; iApply ("HΦ" $! val').
          iFrame "# ∗".
          destruct (decide (ts < val_ts val)); first lia.
          by iFrame "#".
    Qed.

    Theorem tryInsert_spec (key v ts h: Z) (head curr: node_rep) 
      (Smap: gmap Z (argmax Z)) (q: frac)
      (sub: sub_gname) (bot: bot_gname) :
      INT_MIN < key < INT_MAX →
      {{{
        is_bot_list 0 head Smap q bot sub
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < key ⌝
        ∗
        ⌜ 0 ≤ h ⌝ 
      }}}
        tryInsert (rep_to_node curr) #key #v #ts #h
      {{{ (opt: val) (n: loc) (new: node_rep), RET opt;
        is_bot_list 0 head (Smap ⋅ {[ key := prodZ {[ v ]} ts ]}) q bot sub
        ∗
        ( 
          ⌜ opt = NONEV ⌝ ∨ 
          ( 
            ⌜ opt = SOMEV #n ⌝ 
            ∗ 
            own (s_auth sub) (◯ {[ new ]})
            ∗ 
            own (s_toks sub) (GSet {[ node_key new ]})
            ∗ 
            own (s_keys bot) (GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = key ⌝
            ∗
            n ↦□ rep_to_node new
            ∗
            (node_next new +ₗ 1) ↦∗ replicate (Z.to_nat h) #()
            ∗
            (node_locks new +ₗ 1) ↦∗ replicate (Z.to_nat h) #()
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "((Hown_frag & #Hinv) & #Hown_curr & %Hrange & %Hh) HΦ".
      wp_lam. wp_pures.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ l s) "(#Hl & #Hlock & Hnext & #Hs & Hval & Hlocked)".
      do 2 rewrite loc_add_0.

      wp_pures. wp_lam. wp_pures. wp_load. 
      wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (key = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }
        iDestruct "Hval" as "[%Hsucc|Hval]".
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }
        iDestruct "Hval" as (val) "Hval".

        wp_apply (update_spec with "[$]").
        iIntros (val') "((Hown_frag & _) & Hval & _)".
        wp_pures.

        wp_apply (release_spec with "[Hnext Hval Hlocked]").
        { 
          iFrame "# ∗"; iExists s, succ; rewrite loc_add_0; iFrame "# ∗". 
          iRight; by iExists val'.
        }
        iIntros "_". wp_pures.
        iModIntro; iApply "HΦ".
        rewrite -Heq. iFrame "# ∗". by iLeft.
      + assert (key ≠ node_key succ) as Hneq by congruence.

        wp_apply (createAndLink_spec with "[Hnext Hval Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        iIntros (n new) "((Hown_map & _) & Hown_frag & Hown_tok & Hown_key & Hkey & Hnext & #Hn & Hval & Hnexts & Hlocks)".
        wp_let.

        wp_apply (release_spec with "[Hnext Hval Hlocked]").
        { iFrame "# ∗"; iExists n, new; rewrite loc_add_0; iFrame "# ∗". }
        iIntros "_"; wp_pures.
        iModIntro; iApply ("HΦ" $! _ n new).
        iFrame "# ∗". iRight; by iFrame.
    Qed.

    Theorem insert_spec (lvl: Z) (head curr new: node_rep) 
      (bot: bot_gname) (top_sub bot_sub: sub_gname) (n: loc) :
      INT_MIN < node_key new < INT_MAX →
      {{{
        inv (levelN lvl) (lazy_list_inv lvl head bot top_sub (Some bot_sub))
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < node_key new ⌝
        ∗ 
        own (s_auth bot_sub) (◯ {[ new ]})
        ∗ 
        own (s_toks bot_sub) (GSet {[ node_key new ]})
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_next new +ₗ lvl) ↦ #()
        ∗
        (node_locks new +ₗ lvl) ↦ #()
      }}}
        insert (rep_to_node curr) #lvl #n
      {{{ RET #();
        own (s_auth top_sub) (◯ {[ new ]})
        ∗ 
        own (s_toks top_sub) (GSet {[ node_key new ]})
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_curr & %Hrange & Hown_frag & Hown_tok & #Hn & Hnext & Hlocks) HΦ".
      wp_lam. wp_let. wp_let.
      wp_load. wp_lam. wp_pures.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ l s) "(#Hl & #Hlock & Hnext' & #Hs & Hval & Hlocked)".
      wp_pures. wp_lam. wp_pures.

      wp_bind (Load _).
      iInv (levelN lvl) as (S' Smap' L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv' & >Hown_auth & >Hown_toks & Hlist)".
      wp_load.

      iAssert ⌜ node_key new ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro; rewrite Heq /tail/node_key/=; rewrite /node_key in Hkey_range; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.

        assert (In succ L).
        { rewrite -elem_of_list_In Hperm elem_of_elements. set_solver. }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (? ? ? ? ?) "(_ & _ & _ & _ & _ & Hnode & _)".
        iDestruct "Hnode" as "(_ & Hown_tok')".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S', Smap', L; by iFrame "# ∗". }
      iModIntro; wp_pures.

      wp_apply (link_spec with "[Hnext' Hown_frag Hown_tok Hnext Hlocks]").
      { done. }
      { iFrame "# ∗". iPureIntro; lia. }
      iIntros "(Hown_frag & Hown_tok & Hnext)".

      wp_pures.
      wp_apply (release_spec with "[Hnext Hlocked]").
      { iFrame "# ∗"; iExists n, new; iFrame "# ∗". }
      iIntros "_"; iApply "HΦ"; iFrame.
      Unshelve. done.
    Qed.

  End Proofs.
End InsertSpec.