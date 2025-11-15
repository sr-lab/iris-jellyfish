From stdpp Require Import numbers.
From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.jelly_fish Require Import code inv.
From AtomicInvariant.jelly_fish.spec Require Import find.


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
      ⊢ ⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[curr]}) -∗
      <<{ ∀∀ S m, jelly_fish head S m mΓ }>>
        findAll (rep_to_node curr) #k #lvl @ ∅
      <<{ jelly_fish head S m mΓ | RET opt_to_val (m !! k) }>>.
    Proof.
      iIntros "%Hk %Hlvl Hcurr %Φ"; iRevert (lvl curr Hk Hlvl) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Hk Hlvl) "#Hcurr AI".
      rewrite difference_empty_L.
      wp_lam. wp_let. wp_let.

      wp_apply (find_spec with "Hcurr"); first done.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (S m) "Hskip".
      iDestruct (skip_has_lazy with "Hskip") as (S') "[Hlazy [Hskip %Hdom]]"; first done.
      iModIntro. iExists S'. iFrame "Hlazy". iSplit; first done.
      iIntros (pred succ) "[Hlazy %Hkin]". iDestruct ("Hskip" with "Hlazy") as "Hskip".
      iModIntro. iFrame.

      destruct (decide (k = node_key succ)) as [->|Hneq].
      + iLeft. clear dependent S' S m. iIntros "AI".
        iModIntro. iIntros "(Hpred & #Hsucc & %Hk')".
        wp_pures; wp_lam; wp_pures.
        case_bool_decide; last congruence.
        wp_pures; wp_lam; wp_pures.
        wp_bind (Load _). iMod "AI" as (S m) "[Hskip [_ Hclose]]".
        iDestruct "Hsucc" as "[->|Hsucc]"; first (rewrite /node_key/tail/= in Hk; lia).
        iDestruct (node_has_val with "Hskip Hsucc") 
          as (val vl) "(Hval & %Heq & Hskip)"; first done.
        wp_load. iDestruct ("Hskip" with "Hval") as "Hskip".
        iMod ("Hclose" with "Hskip") as "AR".
        iMod (ares_commit with "AR") as "HΦ".
        iModIntro. wp_let; wp_lam; wp_pures.
        destruct val as [[]]; rewrite Heq.
        by iApply "HΦ".
      + destruct (decide (lvl = 0)) as [->|].
        - iRight. iIntros "AR".
          iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
          wp_pures; wp_lam; wp_pures.
          case_bool_decide; first congruence.
          iMod (ares_commit with "AR") as "HΦ".
          assert (m !! k = None) as ->.
          { by apply not_elem_of_dom; rewrite Hdom //= -Hkin. }
          wp_pures. by iApply "HΦ".
        - iLeft.
          clear dependent S S' m. iIntros "AI".
          iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
          wp_pures. wp_lam. wp_pures.
          case_bool_decide; first congruence; wp_pures.
          case_bool_decide; first congruence. wp_pure.
          wp_bind (BinOp _ _ _). iMod "AI" as (S m) "[Hskip [Hclose _]]".
          iDestruct (sent_or_node_in_lower with "Hskip Hpred") as "#Hpred'"; first lia.
          iMod ("Hclose" with "[$]") as "AI".
          wp_pure. iApply (fupd_mask_intro_subseteq _ _ _); first done.
          iApply ("IH" with "[%] [%] Hpred' AI"); first lia; first lia.
    Qed.

    Theorem get_spec (p: loc) (mΓ: gmap Z lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<{ ∀∀ m, vc_map p m mΓ }>> get #p #k @ ∅
      <<{ vc_map p m mΓ | RET opt_to_val (m !! k) }>>.
    Proof.
      iIntros "%Φ AI".
      wp_lam. wp_let.

      wp_bind (Load _). iMod "AI" as (m) "[Hmap [Hclose _]]".
      iDestruct "Hmap" as (head S) "(#Hhead & %Hmin & Hskip)".
      wp_load. iDestruct ("Hclose" with "[Hskip]") as ">AI".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent m S.

      wp_apply findAll_spec; first lia; first (pose HMAX_HEIGHT; lia); first by iLeft.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>"  (m) "Hmap".
      iDestruct (map_has_skip with "Hhead Hmap") as (S) "[Hskip Hmap]".
      iModIntro. iExists S, m. iFrame "Hskip". iSplit; first done.
      iIntros "Hskip". iDestruct ("Hmap" with "Hskip") as "Hmap".
      iModIntro. iFrame. iRight. iIntros "AR".
      iMod (ares_commit with "AR") as "HΦ".
      by iModIntro.
    Qed.
  End Proofs.
End GetSpec.