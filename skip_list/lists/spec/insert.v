From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.lists Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.lists.inv Require Import list_equiv lazy_inv skip_inv. 
From SkipList.skip_list.lists.spec Require Import link.


Local Open Scope Z.

Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Link := LinkSpec Params.
  Export Link.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ} (N : namespace).

    Theorem tryInsert_spec (k: Z) (head curr: node_rep)
      (Skeys: gset Z) (q: frac)
      (bot: bot_gname) (Γ: sub_gname) :
      INT_MIN < k < INT_MAX →
      {{{
        inv N (lazy_list_inv head (Some bot) Γ None)
        ∗
        own (s_frac bot) (◯F{q} Skeys)
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < k ⌝
      }}}
        tryInsert (rep_to_node curr) #k
      {{{ v new, RET v;
        own (s_frac bot) (◯F{q} (Skeys ∪ {[ k ]}))
        ∗
        ( 
          ⌜ v = NONEV ⌝ ∨ 
          ( 
            ⌜ v = SOMEV (rep_to_node new) ⌝ 
            ∗ 
            own (s_auth Γ) (◯ {[ new ]})
            ∗ 
            own (s_toks Γ) (◯ GSet {[ node_key new ]})
            ∗ 
            ⌜ node_key new = k ⌝
          )
        )
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & Hown_frag & #Hown_curr & %Hrange) HΦ".
      wp_lam. wp_let.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γ) "(#Hlock & Hpt & Hlocked)".

      wp_pures. wp_lam. wp_pures. wp_lam. wp_pures.
      case_bool_decide as Hcase; wp_if.
      + assert (k = node_key succ) as Heq by congruence.
        iDestruct "Hown_succ" as "[Hown_succ|%Hsucc]"; last first.
        { subst; exfalso. rewrite /node_key/tail/= in Hkey_range; lia. }

        wp_apply (release_spec with "[Hlock Hpt Hlocked]").
        { iFrame "# ∗"; iExists succ; iFrame. }
        iIntros "_". wp_pures.

        iInv N as (S L) "(Hinv_sub & >Hown_frac)" "Hclose".
        iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".

        iDestruct (own_valid_2 with "Hown_auth Hown_succ") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        iDestruct (own_valid_2 with "Hown_frac Hown_frag") 
          as %Hsub%frac_auth_included_total%gset_included.
        iMod (own_update_2 with "Hown_frac Hown_frag") as "[Hown_frac Hown_frag]".
        { apply frac_auth_update, (gset_local_update_union _ _ {[ k ]}). }
        assert (set_map node_key S ∪ {[ k ]} = set_map node_key S) as -> by set_solver.

        iMod ("Hclose" with "[Hlist Hown_auth Hown_toks Hown_frac]") as "_".
        { iNext; iExists S, L; by iFrame. }
        iModIntro. iApply "HΦ".
        iFrame "# ∗". by iLeft.
      + assert (k ≠ node_key succ) as Hneq by congruence.

        wp_apply (link_bot_spec with "[Hpt Hown_frag]").
        { done. }
        { iFrame "# ∗". iPureIntro; lia. }
        iIntros (new) "(Hlazy & Hown_frag & Hown_tok & Hkey & Hpt)".
        wp_let.

        wp_apply (release_spec with "[Hlock Hpt Hlocked]").
        { iFrame "# ∗"; iExists new; iFrame. }
        iIntros "_"; wp_pures.
        iModIntro; iApply "HΦ".
        iFrame. iRight; by iFrame.
    Qed.

    Theorem insert_spec (head down curr: node_rep) 
      (Γ γ: sub_gname) :
      INT_MIN < node_key down < INT_MAX →
      {{{
        inv N (lazy_list_inv head None Γ (Some γ))
        ∗
        (⌜ curr = head ⌝ ∨ own (s_auth Γ) (◯ {[ curr ]}))
        ∗
        ⌜ node_key curr < node_key down ⌝
        ∗ 
        own (s_auth γ) (◯ {[ down ]})
        ∗ 
        own (s_toks γ) (◯ GSet {[ node_key down ]})
      }}}
        insert (rep_to_node curr) (rep_to_node down)
      {{{ new, RET rep_to_node new;
        own (s_auth Γ) (◯ {[ new ]})
        ∗ 
        own (s_toks Γ) (◯ GSet {[ node_key new ]})
        ∗ 
        ⌜ node_key new = node_key down ⌝
      }}}.
    Proof.
      iIntros (Hkey_range Φ) "(#Hinv & #Hown_curr & %Hrange & #Hown_down & Hown_tok) HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      wp_apply findLock_spec.
      { iFrame "#". iPureIntro; lia. }
      iIntros (pred succ) "(%Hrange' & #Hown_pred & #Hown_succ & Hlock)".
      iDestruct "Hlock" as (γl) "(#Hlock & Hpt & Hlocked)".
      wp_let.

      wp_bind (Fst _).
      iInv N as (S L) "(Hinv_sub & _)" "Hclose".
      iDestruct "Hinv_sub" as "(>%Hperm & >%Hsort & >Hown_auth & >Hown_toks & Hlist)".
      wp_proj.

      iAssert ⌜ node_key down ≠ node_key succ ⌝%I
        with "[Hown_auth Hown_succ Hown_tok Hlist]" as %Hneq.
      {
        iDestruct "Hown_succ" as "[Hown|%Heq]"; last first.
        { iPureIntro. rewrite Heq/node_key/=; rewrite /node_key/= in Hkey_range; lia. } 

        iDestruct (own_valid_2 with "Hown_auth Hown") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.

        assert (In succ L).
        { rewrite -elem_of_list_In Hperm elem_of_elements. set_solver. }

        rewrite list_equiv_invert_L; last done.
        iDestruct "Hlist" as (? ?) "(_ & _ & _ & Hnode & _)".
        destruct (node_down succ) as [d|]; last by iExFalso.
        iDestruct "Hnode" as (?) "(_ & _ & Hown_tok' & %Hsucc)".

        iDestruct (own_valid_2 with "Hown_tok Hown_tok'") as 
          %Hdisj%auth_frag_op_valid_1%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      iMod ("Hclose" with "[Hlist Hown_auth Hown_toks]") as "_".
      { iNext; iExists S, L; by iFrame "# ∗". }
      iModIntro; wp_pures. 
      wp_lam. wp_pures.
      wp_alloc d as "Hpt_down". 
      wp_pures.

      wp_apply (link_top_spec with "[Hpt Hpt_down Hown_tok]").
      { done. }
      { 
        iFrame "# ∗". iSplit; first (iPureIntro; lia). 
        iExists down; by iFrame "# ∗".
      }
      iIntros (new) "(Hlazy & Hown_frag & Hown_tok & Hpt)".

      wp_let.
      wp_apply (release_spec with "[Hlock Hpt Hlocked]").
      { iFrame "# ∗"; iExists new; iFrame. }
      iIntros "_"; wp_pures.
      iModIntro; iApply "HΦ"; iFrame.
    Qed.

  End Proofs.
End InsertSpec.