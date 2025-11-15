From AtomicInvariant.lib Require Import zrange.
From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode notation.
From AtomicInvariant.examples.jelly_fish Require Import code inv.
From AtomicInvariant.examples.jelly_fish.spec Require Import insert.


Module PutSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Insert := InsertSpec Params.
  Export Insert.

  Section Proofs.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    Theorem findLevel_spec (k lvl h: Z) (head curr: node_rep) (mΓ: gmap Z lazy_gname) :
      node_key curr < k < INT_MAX →
      lvl ≤ MAX_HEIGHT →
      0 ≤ h ≤ lvl →
      ⊢ ⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[ curr ]}) -∗
      <<{ ∀∀ S m, jelly_fish head S m mΓ }>>
        findLevel (rep_to_node curr) #k #lvl #h @ ∅
      <<{ ∃∃ pred, jelly_fish head S m mΓ |
        RET (rep_to_node pred);
        (⌜ pred = head ⌝ ∨ own (mΓ !!! h).(auth_gname) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < INT_MAX ⌝
      }>>.
    Proof.
      iIntros "%Hk %Hlvl %Hh Hcurr %Φ"; iRevert (lvl curr Hk Hlvl Hh) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Hk Hlvl Hh) "#Hcurr AI".
      wp_lam; wp_pures.

      wp_apply (find_spec with "Hcurr"); first done.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (S m) "Hskip".
      iDestruct (skip_has_lazy lvl with "Hskip")
        as (S') "[Hlazy [Hskip %Hdom]]"; first lia.
      iModIntro. iExists S'. iFrame "Hlazy". iSplit; first done.
      iIntros (pred succ) "[Hlazy %Hkin]".
      iModIntro. iDestruct ("Hskip" with "Hlazy") as "Hskip".      
      destruct (decide (lvl = h)) as [->|Hneq].
      + iRight. iExists pred. iFrame "Hskip".
        iIntros "AR". iMod (ares_commit with "AR") as "HΦ".
        iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
        wp_pures.
        case_bool_decide; last congruence; wp_if.
        rewrite difference_empty_L.
        iApply "HΦ". iFrame "Hpred". iPureIntro; lia.
      + iLeft. iFrame "Hskip".
        clear dependent S S' m. iIntros "AI".
        iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
        wp_pures. case_bool_decide; first congruence; wp_pure.
        wp_bind (BinOp _ _ _). iMod "AI" as (S m) "[Hskip [Hclose _]]".
        iDestruct (sent_or_node_in_lower with "Hskip Hpred") as "#Hpred'"; first lia.
        iMod ("Hclose" with "[$]") as "AI".
        wp_pure. iApply (fupd_mask_intro_subseteq _ _ _); first done.
        iApply ("IH" with "[%] [%] [%] Hpred' AI"); lia.
    Qed.

    Theorem insertAll_spec (k v t h lvl: Z) (head curr: node_rep) (mΓ: gmap Z lazy_gname) :
      node_key head < k < INT_MAX →
      node_key curr < k →
      lvl ≤ MAX_HEIGHT →
      0 ≤ lvl ≤ h →
      ⊢ ⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[ curr ]}) -∗
      <<{ ∀∀ S m, jelly_fish head S m mΓ }>>
        insertAll (rep_to_node curr) #k #v #t #h #lvl @ ∅
      <<{ ∃∃ opt S', jelly_fish head S' (case_map m k v t) mΓ ∗
          match m !! k with 
          | None => ∃ (n: loc) (new: node_rep),
                      ⌜ opt = SOMEV #n ⌝ ∗ n ↦□ rep_to_node new ∗ ⌜ S' = S ∪ {[ new ]} ⌝
          | Some _ => ⌜ opt = NONEV ⌝ ∗ ⌜ S' = S ⌝
          end |
        RET opt;
        ∀ (n: loc), ⌜ opt = SOMEV #n ⌝ -∗ ∃ (new: node_rep),
          n ↦□ rep_to_node new ∗ ⌜ node_key new = k ⌝ ∗ has_sub (mΓ !!! lvl) new
          ∗
          (node_next new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
          ∗
          (node_lock new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #false
      }>>.
    Proof.
      iIntros "%Hk %Hk' %Hlvl %Hh Hcurr %Φ"; iRevert (lvl curr Φ Hk Hk' Hlvl Hh) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Φ Hk Hk' Hlvl Hh) "#Hcurr AI".
      wp_lam; wp_pures.

      case_bool_decide as Hcase; wp_if.
      + replace lvl with 0 by congruence.
        wp_apply (tryInsert_spec with "Hcurr"); try done; first lia.
        iApply (ainv_ainv with "AI"); try done.
        iIntros "!>" (S m) "[Hmap Hskip]".
        iModIntro. iExists S, m. iFrame "Hmap". iSplit; first by iIntros; iFrame.
        iIntros (opt S') "[Hmap Hmatch]".
        iModIntro. iFrame. iRight. iExists opt, S'. iFrame.
        iIntros "AR". iMod (ares_commit with "AR") as "HΦ".
        iModIntro. iIntros "H". iApply "HΦ". iIntros (n) "#Hopt".
        iDestruct ("H" with "Hopt") as (new) "H"; iExists new.
        replace (h - 0) with h by lia; rewrite ?Loc.add_0 //.
      + assert (lvl ≠ 0) as Hneq by congruence.
        wp_bind (BinOp _ _ _). iMod "AI" as (S m) "[Hskip [Hclose _]]".
        iDestruct (sent_or_node_in_lower with "Hskip Hcurr") as "#Hcurr'"; first lia.
        wp_op. iMod ("Hclose" with "Hskip") as "AI". 
        clear dependent S m. iModIntro.

        wp_apply (find_spec with "Hcurr'"); first lia.
        iApply (ainv_ainv with "AI"); try done.
        iIntros "!>" (S m) "Hskip".
        iDestruct (skip_has_lazy (lvl - 1) with "Hskip") as (S') "[Hlazy [Hskip _]]"; first lia.
        iModIntro. iExists S'. iFrame "Hlazy". iSplit; first done.
        iIntros (pred succ) "[Hlazy _]".
        iModIntro. iDestruct ("Hskip" with "Hlazy") as "Hskip".
        iLeft. iFrame "Hskip". clear dependent S S' m.
        iIntros "AI". iModIntro. iIntros "(Hpred & #Hsucc & %Hk'')".
        wp_pures.

        wp_bind (insertAll _ _ _ _ _ _).
        iApply ("IH" with "[%] [%] [%] [%] Hpred"); try lia.
        iApply (ainv_ainv with "AI"); try done.
        iIntros "!>" (S m) "Hskip".
        iModIntro. iExists S, m. iFrame "Hskip". iSplit; first by iIntros.
        iIntros (opt S') "[Hskip #Hmatch]". iModIntro.
        iRight. iExists opt, S'. iFrame "Hskip Hmatch".
        iIntros "AR". iModIntro. iIntros "Hres".
        wp_pures.

        destruct (m !! k).
        - iDestruct "Hmatch" as "[-> _]". wp_pures.
          rewrite difference_empty_L.
          iMod (ares_commit with "AR") as "HΦ".
          iModIntro. iApply "HΦ". iIntros. congruence.
        - iDestruct "Hmatch" as (n new) "(Hopt & #Hn & _)".
          iDestruct ("Hres" with "Hopt") as (new') "(#Hn' & <- & Hsub & Hnexts & Hlocks)".
          iDestruct (pointsto_agree with "Hn Hn'") as %<-%rep_to_node_inj.
          iDestruct "Hopt" as %->. wp_pures.
          replace (Z.to_nat (h - (lvl - 1))) with (Datatypes.S (Z.to_nat (h - lvl))) by lia.
          rewrite ?(Loc.add_assoc _ (lvl - 1)).
          replace (lvl - 1 + 1) with lvl by lia.
          rewrite ?replicate_S ?array_cons.
          iDestruct "Hnexts" as "[Hnext Hnexts]".
          iDestruct "Hlocks" as "[Hlock Hlocks]".

          wp_apply (insert_spec with "Hcurr Hn Hnext Hlock Hsub"); try lia.
          iCombine "Hnexts Hlocks" as "HR".
          iApply (ainv_ares_frame with "AR HR"); try done.
          
          iIntros "!>" (S'' m') "[Hmap Hskip]".
          rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
          iDestruct "Hskip" as "[[%S''' Hlazy] Hskip]".
          iModIntro. iExists (S'''). iFrame "Hlazy". iSplit.
          {
            iIntros "Hlazy". iFrame.
            iApply (big_sepS_delete _ _ lvl); first (rewrite zrange_spec; lia).
            iFrame.
          }
          iIntros "Hlazy !> [Hnexts Hlocks]". iSplitL "Hmap Hskip Hlazy".
          {
            iFrame.
            iApply (big_sepS_delete _ _ lvl); first (rewrite zrange_spec; lia).
            iFrame.
          }
          clear dependent S'' S''' m'.

          iIntros "AR". iMod (ares_commit with "AR") as "HΦ".
          iModIntro. iIntros "Hsub".
          wp_pures. iModIntro.
          iApply "HΦ". iIntros (n' ?); replace n' with n by congruence.
          iExists new. by iFrame "# ∗".
    Qed.

    Theorem putH_spec (p: loc) (k v t h: Z) (mΓ: gmap Z lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX)
      (Hheight: 0 ≤ h ≤ MAX_HEIGHT) :
      ⊢ <<{ ∀∀ m, vc_map p m mΓ }>>
        putH #p #k #v #t #h @ ∅
      <<{
        ∃∃ opt, vc_map p (case_map m k v t) mΓ ∗ ⌜ opt = m !! k ⌝ |
        RET #();
        ⌜ opt = None ⌝ → ∃ new, ⌜ node_key new = k ⌝ ∗ has_sub (mΓ !!! h) new
      }>>.
    Proof.
      iIntros "%Φ AI".
      wp_lam; wp_pures. 
      
      wp_bind (Load _). iMod "AI" as (m) "[Hmap [Hclose _]]".
      iDestruct "Hmap" as (head S) "(#Hhead & %Hmin & Hskip)".
      wp_load. iDestruct ("Hclose" with "[Hskip]") as ">AI".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent m S.

      wp_apply findLevel_spec; try lia; first by iLeft.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (m) "Hmap".
      iDestruct (map_has_skip with "Hhead Hmap") as (S) "[Hskip Hmap]".
      iModIntro. iExists S, m. iFrame "Hskip". iSplit; first done.
      iIntros (pred) "Hskip". iModIntro.
      iLeft. iSplitL; first by iApply "Hmap". clear dependent S m.
      iIntros "AI". iModIntro. iIntros "[Hnode %Hk]".
      wp_pures.

      wp_apply (insertAll_spec with "Hnode"); try lia.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (m) "Hmap".
      iDestruct "Hmap" as (head' S) "(H & _ & Hskip)".
      iDestruct (pointsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iModIntro. iExists S, m. iFrame "Hskip". iSplit; first by iIntros; iFrame "# ∗".
      iIntros (opt S') "[Hskip #Hmatch]". iModIntro.
      iRight. iExists (m !! k). iSplitL.
      { by iSplit; first iExists head, S'; iFrame "# ∗". }
      iIntros "AR". iMod (ares_commit with "AR") as "HΦ".

      iModIntro. iIntros "Hres".
      wp_pures. iModIntro. iApply "HΦ".
      iIntros (->). iDestruct "Hmatch" as (n new) "(Hopt & #Hn & _)".
      iDestruct ("Hres" with "Hopt") as (new') "(#Hn' & <- & Hsub & _)".
        iDestruct (pointsto_agree with "Hn Hn'") as %<-%rep_to_node_inj.
      iExists new. by iFrame.
    Qed.

    Theorem put_spec (p: loc) (k v t: Z) (mΓ: gmap Z lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<{ ∀∀ m, vc_map p m mΓ }>> 
        put #p #k #v #t @ ∅ 
      <<{ vc_map p (case_map m k v t) mΓ | RET #() }>>.
    Proof.
      iIntros "%Φ AI". pose proof HMAX_HEIGHT.
      wp_lam; wp_pures; wp_lam; wp_pures.
      wp_apply putH_spec; try lia.
      iApply (ainv_ainv with "AI"); try done.
      iIntros "!>" (m) "Hmap".
      iModIntro. iExists m. iFrame "Hmap". iSplit; first by iIntros.
      iIntros (?) "[Hmap _ ]". iModIntro. iRight. iFrame.
      iIntros "AR". iMod (ares_commit with "AR") as "HΦ".
      iModIntro. iIntros "_". by iApply "HΦ".
    Qed.
  End Proofs.
End PutSpec.