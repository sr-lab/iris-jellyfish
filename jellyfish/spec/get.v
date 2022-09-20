From iris.algebra Require Import auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jellyfish.spec Require Import find.


Local Open Scope Z.

Module GetSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ}.
    
    Theorem findAll_spec (k lvl: Z) (head curr: node_rep) 
      (M: gmap Z (argmax Z)) (bot: bot_gname) 
      (top_sub: sub_gname) (bot_subs: list sub_gname) :
      {{{ 
        skip_list_equiv lvl head M 1 bot (top_sub :: bot_subs)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth top_sub) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k < INT_MAX ⌝
      }}}
        findAll (rep_to_node curr) #k #lvl #0
      {{{ pred succ sub, RET ((rep_to_node pred), (rep_to_node succ));
        skip_list_equiv lvl head M 1 bot (top_sub :: bot_subs)
        ∗
        ⌜ last (top_sub :: bot_subs) = Some sub ⌝
        ∗
        (own (s_auth sub) (◯ {[ succ ]}) ∨ ⌜ succ = tail ⌝)
        ∗
        ⌜ k ∈ dom M ↔ node_key succ = k ⌝
      }}}.
    Proof.
      iIntros (Φ) "(Hlist & Hown_curr & Hrange) HΦ".
      iRevert (curr head lvl top_sub bot_subs) "Hlist Hown_curr Hrange HΦ".
      iLöb as "IH".
      iIntros (curr head lvl top_sub bot_subs) "Hlist #Hown_curr %Hrange HΦ".
      wp_lam. wp_let. wp_let. wp_let.
      
      destruct bot_subs as [|bot_sub].
      + iDestruct "Hlist" as "(%Hlvl & (Hown_frag & #Hinv))"; rewrite Hlvl.
        wp_apply (find_bot_spec with "[Hown_frag]").
        { by iFrame "# ∗". }
        iIntros (pred succ) "(Hown_frag & %Hpred_key & #Hown_succ & %Hkey_in_S)".

        wp_pures.
        iModIntro; iApply "HΦ". 
        by iFrame "# ∗".
      + iDestruct "Hlist" as "(%Hlvl & #Hinv & Hmatch)".
        wp_apply find_sub_spec.
        { by iFrame "# ∗". }
        iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & _)".

        wp_pures. case_bool_decide as Hcase; wp_if.
        - exfalso; inversion Hcase; lia.
        - wp_bind (BinOp _ _ _).
          iInv (levelN lvl) as (M' S L) "(Hinv_sub & _)" "Hclose".
          iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".

          iDestruct "Hown_pred" as "[%Heq | #Hown_pred]".
          * wp_op.            
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists M', S, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [] [%]").
            { by iLeft. }
            { lia. }
            iNext; iIntros (? ? ?) "(? & ? & ? & ?)".
            iApply "HΦ". by iFrame "# ∗".
          * iAssert ⌜ In pred L ⌝%I with "[Hown_auth]" as %Hin.
            {
              iDestruct (own_valid_2 with "Hown_auth Hown_pred") 
                as %[Hvalid%gset_included]%auth_both_valid_discrete.
              rewrite -elem_of_list_In Hperm elem_of_elements.
              iPureIntro; set_solver.
            }

            rewrite list_equiv_invert_L; last done.
            iDestruct "Hlist" as (v γ l s' succ') "(>%Hsucc'_range & Hpt' & #Hs' & #Hl & #Hlock & Hnode & _ & Himp)".
            iDestruct "Hnode" as"(>Hauth_pred & >Htoks_pred)".

            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as -> by set_solver.
            iDestruct "Hauth_pred" as "(Hauth_pred & Hauth_pred_dup)".
            assert ({[ pred ]} = {[ pred ]} ⋅ {[ pred ]}) as <- by set_solver.

            wp_op.
            iPoseProof ("Himp" $! {[ val_v dummy_val ]} dummy_val with "[Hpt' Hauth_pred_dup Htoks_pred]") as "Hlist".
            { iFrame; rewrite elem_of_singleton //. }
            iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
            { iNext; iExists M', S, L; by iFrame. }

            iModIntro; wp_pures.
            iApply ("IH" with "[$] [Hauth_pred] [%]").
            { by iRight. }
            { lia. }
            iNext; iIntros (? ? ?) "(? & ? & ? & ?)".
            iApply "HΦ". by iFrame "# ∗".
    Qed.
    
    Theorem get_spec (p: loc) (k: Z) (M: gmap Z (argmax Z)) 
      (bot: bot_gname) (subs: list sub_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      {{{ is_skip_list p M 1 bot subs }}}
        get #p #k
      {{{ v, RET v;
        is_skip_list p M 1 bot subs ∗ ((⌜ v = NONEV ⌝ ∗ ⌜ M !! k = None ⌝) ∨
        ∃ (t z: Z) (S: gset Z), ⌜ v = SOMEV (#z, #t) ⌝ ∗ ⌜ M !! k = Some (prodZ S t) ⌝ ∗ ⌜ z ∈ S ⌝)
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (head) "(Hpt & %Hmin & Hlist)".
      wp_lam. wp_let. wp_load.

      destruct subs as [|sub subs]; first by iExFalso.
      wp_apply (findAll_spec with "[Hlist]").
      { iFrame. iSplit. by iLeft. iPureIntro; lia. }
      iIntros (pred succ bot_sub) "(Hlist & %Hlast & #Hown & %Hkey_in_dom)".
      wp_pures. wp_lam. wp_pures.
      
      case_bool_decide as Hcase; wp_if.
      + wp_lam. wp_pures.
        rewrite skip_list_equiv_inv.
        iDestruct "Hlist" as (bot_sub') "(%Hlast' & (Hown_frag & #Hinv) & Himp)".
        assert (bot_sub = bot_sub') as <- by congruence.

        wp_bind (Load _).
        iInv (levelN 0) as (? S L) "(Hinv_sub & >Hown_frac)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >%Hequiv & >Hown_auth & >Hown_toks & Hlist)".
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %->%frac_auth_agree_L.

        iAssert ⌜ In succ L ⌝%I with "[Hown_auth]" as %Hsucc.
        {
          iDestruct "Hown" as "[Hown|%Hfalse]"; last first.
          {
            assert (k = node_key tail) as -> by congruence.
            rewrite /tail/node_key/= in Hrange; lia.
          }

          iDestruct (own_valid_2 with "Hown_auth Hown") 
            as %[Hvalid%gset_included]%auth_both_valid_discrete.
          rewrite -elem_of_list_In Hperm elem_of_elements.
          iPureIntro; set_solver.
        }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (v' γ' l' s' succ') "(_ & Hpt' & _ & _ & _ & Hnode & >%Hval & Himp')".
        destruct Hval as [vs [Hsome Hin]].
        
        wp_load.
        iPoseProof ("Himp'" $! vs v' with "[Hpt' Hnode]") as "Hlist".
        { by iFrame. }
        rewrite /opt_map /opt_insert insert_id //.
        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists M, S, L; by iFrame. }
        iPoseProof ("Himp" with "[$]") as "Hlist".

        iModIntro; wp_pures.
        iModIntro; iApply "HΦ". 
        iSplit.
        { iExists head; by iFrame. }

        iPureIntro; right.
        exists (val_ts v'), (val_v v'), vs.
        inversion Hcase; subst.
        rewrite //.
      + iModIntro; iApply "HΦ". 
        iSplit. 
        { iExists head; by iFrame. }
        
        iPureIntro; left.
        split; first done.
        rewrite -not_elem_of_dom. intros Hin. 
        rewrite Hkey_in_dom in Hin. congruence.
    Qed.

  End Proofs.
End GetSpec.