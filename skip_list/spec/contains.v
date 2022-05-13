From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import inv node_rep code key_equiv.
From SkipList.skip_list.spec Require Import find.


Local Open Scope Z.
Module ContainsSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Import Find.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).
    
    Theorem findPred_spec (head curr: node_rep) (key: Z) (S: gset node_rep) :
      {{{ 
        inv N (skip_list_inv head S)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        findPred (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
      }}}.
    Proof.
    Admitted.
    
    Theorem contains_spec (v: val) (key: Z) (Skeys: gset Z)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_skip_list N v Skeys }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_skip_list N v Skeys
        ∗
        ⌜ if b then key ∈ Skeys else key ∉ Skeys ⌝
      }}}.
    Proof.
      iIntros (Φ) "H HΦ".
      iDestruct "H" as (h head S) "(%Hequiv & %Hv & Hpt & %Hmin & #Hinv)".
      wp_lam. wp_let. rewrite -Hv. wp_load.
      wp_apply (findPred_spec).
      { iFrame "# ∗". iPureIntro; split. by left. lia. }
      iIntros (pred succ) "%Hkey_in_S".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.

      iModIntro; case_bool_decide.
      + iApply "HΦ". iSplit.
        - iExists h, head, S. by iFrame "# ∗".
        - iPureIntro. rewrite /key_equiv in Hequiv. 
          rewrite -elem_of_elements Hequiv Hkey_in_S.
          congruence.
      + iApply "HΦ". iSplit. 
        - iExists h, head, S. by iFrame "# ∗".
        - iPureIntro. intros Hin. 
          rewrite -elem_of_elements Hequiv Hkey_in_S in Hin.
          congruence.
    Qed.

  End Proofs.
End ContainsSpec.