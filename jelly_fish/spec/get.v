From stdpp Require Import numbers.
From iris.heap_lang Require Import notation.

From SkipList.atomic Require Import weakestpre proofmode.
From SkipList.jelly_fish Require Import code inv.
From SkipList.jelly_fish.spec Require Import find.


Module GetSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Section Proofs.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    Definition opt_to_val (opt: option (tval * list tval)) : val :=
      match opt with
      | None => NONEV
      | Some (v, t, vl) => SOMEV (#v, #t)
      end.

    Theorem findAll_spec (k lvl: Z) (head curr: node_rep) (mΓ: gmap Z lazy_gname) :
      node_key curr < k < INT_MAX →
      0 ≤ lvl ≤ MAX_HEIGHT →
      (⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[curr]})) -∗
      <<< ∀∀ S m, jelly_fish head S m mΓ >>>
        findAll (rep_to_node curr) #k #lvl @ ∅
      <<< jelly_fish head S m mΓ, RET opt_to_val (m !! k) >>>
      {{{ True }}}.
    Proof.
      iIntros "%Hk %Hlvl Hcurr %Φ"; iRevert (lvl curr Hk Hlvl) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Hk Hlvl) "#Hcurr AU".
      rewrite difference_empty_L.
      wp_lam. wp_let. wp_let.

      awp_apply (find_spec with "Hcurr"); first done.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      {
        iIntros "!> %S %m Hskip".
        iDestruct (skip_has_lazy with "Hskip") as (S') "[Hlazy [Hskip _]]"; first done.
        iExists S'. iFrame.
      }
      iIntros (S m) "Hskip".
      iDestruct (skip_has_lazy with "Hskip") as (S') "[Hlazy [Hskip %Hdom]]"; first done.
      iAaccIntro with "Hlazy".
      { iIntros "H"; iDestruct ("Hskip" with "H") as "Hskip". iModIntro; iFrame; by iIntros. }
      iIntros (pred succ) "[Hlazy %Hkin]".
      iModIntro. iExists S'. iFrame "Hlazy". iIntros "Hlazy".

      destruct (decide (k = node_key succ)) as [->|Hneq].
      + iLeft. iDestruct ("Hskip" with "Hlazy") as "Hskip". iFrame.
        clear dependent S S' m. iIntros "AU".
        iModIntro. iIntros "(Hpred & #Hsucc & %Hk')".
        iModIntro. wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence.
        wp_pures; wp_lam; wp_pures.
        wp_bind (Load _). iMod "AU" as (S m) "[Hskip [_ Hclose]]".
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/tail/= in Hk; lia).
        iDestruct (node_has_val with "Hskip Hsucc") 
          as (val vl) "(Hval & %Heq & Hskip)"; first done.
        wp_load. iDestruct ("Hskip" with "Hval") as "Hskip".
        iMod ("Hclose" with "Hskip") as "AP".
        destruct val as [[]]; rewrite Heq.
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. wp_let; wp_lam; wp_pures.
        by iApply "HΦ".
      + destruct (decide (lvl = 0)) as [->|].
        - iRight. iDestruct ("Hskip" with "Hlazy") as "Hskip". iFrame.
          assert (m !! k = None) as ->.
          { by apply not_elem_of_dom; rewrite Hdom //=; apply Hkin. }
          clear dependent S S' m. iIntros "AP".
          iMod (atomic_post_commit with "AP") as "HΦ".
          iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
          iModIntro. wp_pures; wp_lam; wp_pures.
          case_bool_decide; first congruence.
          wp_pures. by iApply "HΦ".
        - iLeft. iDestruct ("Hskip" with "Hlazy") as "Hskip". iFrame.
          clear dependent S S' m. iIntros "AU".
          iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
          iMod "AU" as (S m) "[Hskip [Hclose _]]".
          iDestruct (sent_or_node_in_lower with "Hskip Hpred") as "#Hpred'"; first lia.
          iMod ("Hclose" with "[$]") as "AU".
          iModIntro. wp_pures; wp_lam; wp_pures.
          do 2 (case_bool_decide; first congruence; wp_pures).
          iApply ("IH" with "[%] [%] Hpred' AU"); first lia; first lia.
    Qed.

    Theorem get_spec (p: loc) (mΓ: gmap Z lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<< ∀∀ m, vc_map p m mΓ >>>
        get #p #k @ ∅
      <<< vc_map p m mΓ, RET opt_to_val (m !! k) >>>
      {{{ True }}}.
    Proof.
      iIntros (Φ) "AU".
      wp_lam. wp_let.

      wp_bind (Load _). iMod "AU" as (m) "[Hmap [Hclose _]]".
      iDestruct "Hmap" as (head S) "(#Hhead & %Hmin & Hskip)".
      wp_load. iDestruct ("Hclose" with "[Hskip]") as ">AU".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent m S.

      awp_apply (findAll_spec with "[]"); 
        first lia; first (pose HMAX_HEIGHT; lia); first by iLeft.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { 
        iIntros "!> %m Hmap". 
        iDestruct (map_has_skip with "Hhead Hmap") as (S) "?". 
        iExists S, m. iFrame. 
      }
      iIntros (m) "Hmap". 
      iDestruct (map_has_skip with "Hhead Hmap") as (S) "[Hskip Hmap]".
      iAaccIntro with "Hskip".
      { iIntros "H"; iDestruct ("Hmap" with "H") as "Hmap"; iModIntro; iFrame; by iIntros. }
      iIntros "H". iModIntro. iExists S, m. iFrame "H".
      iIntros "Hskip". iDestruct ("Hmap" with "Hskip") as "Hmap".
      iRight. iFrame "Hmap". iIntros "AP".
      by iMod (atomic_post_commit with "AP") as "HΦ".
    Qed.
  End Proofs.
End GetSpec.