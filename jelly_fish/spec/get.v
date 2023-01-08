From iris.algebra Require Import gmap gset excl_auth dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange gmap_extra.
From SkipList.jelly_fish Require Import code inv.
From SkipList.jelly_fish.spec Require Import find.


Local Open Scope Z.

Module GetSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipG Σ} (N: namespace).

    Definition opt_to_val (opt: option (Z * Z)) : val :=
      match opt with
      | None => NONEV
      | Some vt => SOMEV (#vt.1, #vt.2)
      end.

    Theorem findAll_spec (k lvl: Z) (head curr: node_rep) (Γm: map_gname) (Γ: gmap Z inv_gname) :
      node_key curr < k < INT_MAX →
      0 ≤ lvl ≤ MAX_HEIGHT →
      (⌜ curr = head ⌝ ∨ own (Γ !!! lvl).(auth_gname) (◯ {[curr]})) -∗
      inv (skipN N) (skip_list_inv head Γm Γ) -∗
      <<< ∀∀ (m: gmap Z (Z * Z)), map m Γm >>>
        findAll (rep_to_node curr) #k #lvl @ ↑(skipN N)
      <<< map m Γm, RET opt_to_val (m !! k) >>>.
    Proof.
      iIntros "%Hk %Hlvl Hcurr #Hinv %Φ"; iRevert (lvl curr Hk Hlvl) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Hk Hlvl) "#Hcurr AU".
      wp_lam. wp_let. wp_let.

      awp_apply (find_spec with "Hcurr Hinv"); first done; first done.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (m) "(Hexcl◯ & Hvals)"; iAaccIntro with "Hexcl◯".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros (pred succ) "(Hexcl◯ & %Hnin & #Hpred & #Hsucc & %Hk' & Hlock)".
      iDestruct "Hlock" as (γl l) "(#Hlock & #His_lock)".

      destruct (decide (k = node_key succ)) as [->|Hneq].
      + iModIntro; iLeft; iFrame.
        iIntros "AU"; iModIntro.
        wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence.
        wp_pures; wp_lam; wp_pures.

        wp_bind (Load _). iInv "Hinv" as "Hskip".
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/= in Hk; lia).
        iDestruct (frag_has_val with "Hskip []") as "(>Hval & Hskip)"; first done.
        { by iNext. }

        clear dependent m; iMod "AU" as (m) "[(Hexcl◯ & Hvals●) [_ Hclose]]".
        iDestruct "Hval" as (v) "(Hpt & Hval)".
        iDestruct (own_valid_2 with "Hvals● Hval") 
          as %[->%gmap_disj_included%map_singleton_subseteq_l]%auth_both_valid_discrete.

        wp_load.
        iDestruct ("Hclose" with "[$]") as ">HΦ"; last iModIntro.
        iModIntro; iSplitL "Hskip Hpt Hval".
        { iNext; iApply "Hskip"; iExists v; iFrame. }
        by wp_let; wp_lam; wp_pures.
      + destruct (decide (lvl = 0)) as [->|].
        - iModIntro; iRight; iFrame.
          iIntros "HΦ"; iModIntro.
          wp_pures; wp_lam; wp_pures.
          case_bool_decide; first congruence.
          wp_pures; iModIntro. 
          replace (m !! k) with (@None (Z * Z)); first done.
          symmetry; by apply not_elem_of_dom, Hnin.
        - iModIntro; iLeft; iFrame.
          iIntros "AU"; iModIntro.
          wp_pures; wp_lam; wp_pures.
          do 2 (case_bool_decide; first congruence; wp_pures).
          iDestruct (has_lower_frag with "Hinv Hpred") as ">Hpred'"; first lia.          
          by iApply ("IH" with "[%] [%] Hpred'"); first lia; first lia.
    Qed.

    Theorem get_spec (p: loc) (Γm: map_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      map_inv N p Γm -∗
      <<< ∀∀ (m: gmap Z (Z * Z)), map m Γm >>>
        get #p #k @ ↑(skipN N)
      <<< map m Γm, RET opt_to_val (m !! k) >>>.
    Proof.
      iIntros "#H %Φ AU".
      iDestruct "H" as (head Γ) "(Hp & %Hmin & #Hinv)".
      wp_lam. wp_let. wp_load.

      awp_apply (findAll_spec with "[] Hinv"); 
        first lia; first (pose HMAX_HEIGHT; lia); first by iLeft.
      iApply (aacc_aupd with "AU"); first done.
      iIntros (m) "Hmap"; iAaccIntro with "Hmap".
      { do 2 (iIntros "?"; iModIntro; iFrame). }
      iIntros. iModIntro; iRight; iFrame. by iIntros.
    Qed.
  End Proofs.
End GetSpec.