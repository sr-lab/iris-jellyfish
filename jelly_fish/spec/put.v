From iris.heap_lang Require Import notation.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import weakestpre proofmode.
From SkipList.jelly_fish Require Import code inv.
From SkipList.jelly_fish.spec Require Import insert.


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
      (⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[ curr ]})) -∗
      <<< ∀∀ S m, jelly_fish head S m mΓ >>>
        findLevel (rep_to_node curr) #k #lvl #h @ ∅
      <<< ∃∃ pred, jelly_fish head S m mΓ, RET (rep_to_node pred) >>>
      {{{ 
        (⌜ pred = head ⌝ ∨ own (mΓ !!! h).(auth_gname) (◯ {[ pred ]}))
        ∗
        ⌜ node_key pred < k < INT_MAX ⌝
      }}}.
    Proof.
      iIntros "%Hk %Hlvl %Hh Hcurr %Φ"; iRevert (lvl curr Hk Hlvl Hh) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Hk Hlvl Hh) "#Hcurr AU".
      wp_lam; wp_pures.

      awp_apply (find_spec with "Hcurr"); first done.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      {
        iIntros "!> %S %m Hskip".
        iDestruct (skip_has_lazy lvl with "Hskip") as (S') "[Hlazy [Hskip _]]"; first lia.
        iExists S'. iFrame.
      }
      iIntros (S m) "Hskip".
      iDestruct (skip_has_lazy lvl with "Hskip") as (S') "[Hlazy [Hskip %Hdom]]"; first lia.
      iAaccIntro with "Hlazy".
      { iIntros "H"; iDestruct ("Hskip" with "H") as "Hskip". iModIntro; iFrame; by iIntros. }
      iIntros (pred succ) "[Hlazy %Hkin]".
      iModIntro. iExists S'. iFrame "Hlazy". iIntros "Hlazy".
      iDestruct ("Hskip" with "Hlazy") as "Hskip".
      
      destruct (decide (lvl = h)) as [->|Hneq].
      + iRight. iExists pred. iFrame "Hskip".
        clear dependent S S' m. iIntros "AP".
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
        iModIntro. wp_pures.
        case_bool_decide; last congruence; wp_if.
        rewrite difference_empty_L.
        iApply "HΦ". iFrame "Hpred". iPureIntro; lia.
      + iLeft. iFrame "Hskip".
        clear dependent S S' m. iIntros "AU".
        iModIntro. iIntros "(Hpred & Hsucc & %Hk')".
        iMod "AU" as (S m) "[Hskip [Hclose _]]".
        iDestruct (sent_or_node_in_lower with "Hskip Hpred") as "#Hpred'"; first lia.
        iMod ("Hclose" with "[$]") as "AU".
        iModIntro. wp_pures.
        case_bool_decide; first congruence; wp_pures.
        iApply ("IH" with "[%] [%] [%] Hpred' AU"); lia.
    Qed.

    Theorem insertAll_spec (k v t h lvl: Z) (head curr: node_rep) (mΓ: gmap Z lazy_gname) :
      node_key head < k < INT_MAX →
      node_key curr < k →
      lvl ≤ MAX_HEIGHT →
      0 ≤ lvl ≤ h →
      (⌜ curr = head ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[ curr ]})) -∗
      <<< ∀∀ S m, jelly_fish head S m mΓ >>>
        insertAll (rep_to_node curr) #k #v #t #h #lvl @ ∅
      <<< ∃∃ opt S',
        jelly_fish head S' (case_map m k v t) mΓ
        ∗
        match m !! k with 
        | None => ∃ (n: loc) (new: node_rep),
                    ⌜ opt = SOMEV #n ⌝ ∗ n ↦□ rep_to_node new ∗ ⌜ S' = S ∪ {[ new ]} ⌝
        | Some _ => ⌜ opt = NONEV ⌝ ∗ ⌜ S' = S ⌝
        end,
      RET opt >>>
      {{{
        ∀ (n: loc), ⌜ opt = SOMEV #n ⌝ -∗ ∃ (new: node_rep),
          n ↦□ rep_to_node new ∗ ⌜ node_key new = k ⌝ ∗ has_sub (mΓ !!! lvl) new
          ∗
          (node_next new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #()
          ∗
          (node_lock new +ₗ lvl +ₗ 1) ↦∗ replicate (Z.to_nat (h - lvl)) #false
      }}}.
    Proof.
      iIntros "%Hk %Hk' %Hlvl %Hh Hcurr %Φ"; iRevert (lvl curr Φ Hk Hk' Hlvl Hh) "Hcurr".
      iLöb as "IH"; iIntros (lvl curr Φ Hk Hk' Hlvl Hh) "#Hcurr AU".
      wp_lam; wp_pures.

      case_bool_decide as Hcase; wp_if.
      + replace lvl with 0 by congruence.
        awp_apply (tryInsert_spec with "Hcurr"); try lia.
        iApply (aacc_aupd_sub with "[] AU"); try done.
        { iIntros "!> %S %m [Hmap Hskip]"; iExists S, m; iFrame; iIntros; iFrame. }
        iIntros (S m) "[Hmap Hskip]"; iAaccIntro with "Hmap".
        { iIntros; iFrame; iModIntro; by iIntros. }
        iIntros (opt S') "[Hmap Hmatch]". iModIntro.
        iExists S', (case_map m k v t).
        iFrame "Hmap". iIntros "Hmap".
        iRight. iExists opt, S'. iFrame "Hmap Hmatch Hskip".
        clear dependent S. iIntros "AP".
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "H". iApply "HΦ". iIntros (n) "#Hopt".
        iDestruct ("H" with "Hopt") as (new) "H"; iExists new.
        replace (h - 0) with h by lia; rewrite ?Loc.add_0 //.
      + assert (lvl ≠ 0) as Hneq by congruence.
        wp_bind (BinOp _ _ _). iMod "AU" as (S m) "[Hskip [Hclose _]]".
        iDestruct (sent_or_node_in_lower with "Hskip Hcurr") as "#Hcurr'"; first lia.
        wp_op. iMod ("Hclose" with "Hskip") as "AU". 
        clear dependent S m. iModIntro.

        awp_apply (find_spec with "Hcurr'"); first lia.
        iApply (aacc_aupd_sub with "[] AU"); try done.
        {
          iIntros "!> %S %m Hskip".
          iDestruct (skip_has_lazy (lvl - 1) with "Hskip") as (S') "[Hlazy [Hskip _]]"; first lia.
          iExists S'. iFrame.
        }
        iIntros (S m) "Hskip".
        iDestruct (skip_has_lazy (lvl - 1) with "Hskip") as (S') "[Hlazy [Hskip _]]"; first lia.
        iAaccIntro with "Hlazy".
        { iIntros "H"; iDestruct ("Hskip" with "H") as "Hskip". iModIntro; iFrame; by iIntros. }
        iIntros (pred succ) "[Hlazy _]".
        iModIntro. iExists S'. iFrame "Hlazy". iIntros "Hlazy".
        iDestruct ("Hskip" with "Hlazy") as "Hskip".

        iLeft. iFrame "Hskip".
        clear dependent S S' m. iIntros "AU".
        iModIntro. iIntros "(Hpred & Hsucc & %Hk'')".
        iModIntro. wp_pures.

        wp_bind (insertAll _ _ _ _ _ _).
        iApply ("IH" with "[%] [%] [%] [%] Hpred"); try lia.
        iAuIntro. iApply (aacc_aupd_eq with "AU"); try done.
        iIntros (S m) "Hskip"; iAaccIntro with "Hskip".
        { iIntros; iFrame; iModIntro; by iIntros. }
        iIntros (opt S') "[Hskip #Hmatch]". iModIntro.
        iExists S', (case_map m k v t).
        iFrame "Hskip". iIntros "Hskip".
        iRight. iExists opt, S'. 
        iFrame "Hskip Hmatch". iIntros "AP".
        iModIntro. iIntros "Hres".
        iModIntro. wp_pures.
        
        destruct (m !! k); clear dependent m.
        - iDestruct "Hmatch" as "[-> _]". wp_pures.
          rewrite difference_empty_L.
          iMod (atomic_post_commit with "AP") as "HΦ".
          iApply "HΦ". iIntros. congruence.
        - iDestruct "Hmatch" as (n new) "(Hopt & #Hn & _)".
          iDestruct ("Hres" with "Hopt") as (new') "(#Hn' & <- & Hsub & Hnexts & Hlocks)".
          iDestruct (mapsto_agree with "Hn Hn'") as %<-%rep_to_node_inj.
          iDestruct "Hopt" as %->. wp_pures. clear dependent S S'.
          replace (Z.to_nat (h - (lvl - 1))) with (S (Z.to_nat (h - lvl))) by lia.
          rewrite ?(Loc.add_assoc _ (lvl - 1)).
          replace (lvl - 1 + 1) with lvl by lia.
          rewrite ?replicate_S ?array_cons.
          iDestruct "Hnexts" as "[Hnext Hnexts]".
          iDestruct "Hlocks" as "[Hlock Hlocks]".

          awp_apply (insert_spec with "Hcurr Hn Hnext Hlock Hsub"); try lia.
          iApply (aacc_apst_sub with "[] AP"); try done.
          {
            iIntros "!> %S %m Hskip".
            iDestruct (skip_has_lazy lvl with "Hskip") as (S') "[Hlazy [Hskip _]]"; first lia.
            iExists S'. unfold opt_sub; case_decide; first lia. iFrame.
          }
          iIntros (S m) "[Hmap Hskip]".
          rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
          iDestruct "Hskip" as "[[%S' Hlazy] Hskip]".
          iAaccIntro with "Hlazy".
          { 
            iIntros "Hlazy". iModIntro. iFrame "Hmap".
            iSplitL "Hlazy Hskip"; last (iIntros; iModIntro; iFrame).
            iApply (big_sepS_delete _ _ lvl); first (rewrite zrange_spec; lia).
            iFrame "Hskip". by iExists S'.
          }
          iIntros "Hlazy". iModIntro. iExists (S' ∪ {[ new ]}).
          iFrame "Hlazy". iIntros "Hlazy". iFrame "Hmap".
          iSplitL "Hlazy Hskip".
          {
            iApply (big_sepS_delete _ _ lvl); first (rewrite zrange_spec; lia).
            iFrame "Hskip". by iExists (S' ∪ {[ new ]}).
          }
          clear dependent S S' m. iIntros "AP".
          iMod (atomic_post_commit with "AP") as "HΦ".
          iModIntro. iIntros "Hsub".
          iModIntro. wp_pures.
          rewrite difference_empty_L.
          iApply "HΦ". iIntros (n' ?); replace n' with n by congruence.
          iExists new.  by iFrame "# ∗".
    Qed.

    Theorem putH_spec (p: loc) (k v t h: Z) (mΓ: gmap Z lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX)
      (Hheight: 0 ≤ h ≤ MAX_HEIGHT) :
      ⊢ <<< ∀∀ m, vc_map p m mΓ >>>
        putH #p #k #v #t #h @ ∅
      <<< ∃∃ opt, vc_map p (case_map m k v t) mΓ ∗ ⌜ opt = m !! k ⌝, RET #() >>>
      {{{ ⌜ opt = None ⌝ → ∃ new, ⌜ node_key new = k ⌝ ∗ has_sub (mΓ !!! h) new }}}.
    Proof.
      iIntros (Φ) "AU".
      wp_lam; wp_pures. 
      
      wp_bind (Load _). iMod "AU" as (m) "[Hmap [Hclose _]]".
      iDestruct "Hmap" as (head S) "(#Hhead & %Hmin & Hskip)".
      wp_load. iDestruct ("Hclose" with "[Hskip]") as ">AU".
      { iExists head, S; by iFrame "# ∗". }
      iModIntro; clear dependent m S.

      awp_apply (findLevel_spec); try lia; first by iLeft.
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
      iIntros (pred) "Hskip". iModIntro. iExists S, m.
      iFrame "Hskip". iIntros "Hskip".
      iDestruct ("Hmap" with "Hskip") as "Hmap".
      iLeft. iFrame "Hmap".
      clear dependent S m. iIntros "AU".
      iModIntro. iIntros "[Hnode %Hk]".
      iModIntro. wp_pures.

      awp_apply (insertAll_spec with "Hnode"); try lia.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { 
        iIntros "!> %m Hmap". 
        iDestruct (map_has_skip with "Hhead Hmap") as (S) "?". 
        iExists S, m. iFrame. 
      }
      iIntros (m) "Hmap".
      iDestruct "Hmap" as (head' S) "(H & _ & Hskip)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iAaccIntro with "Hskip".
      { 
        iIntros "Hskip". iModIntro. iSplitR ""; last (iIntros; iModIntro; iFrame).
        iExists head, S. by iFrame "# ∗".
      }
      iIntros (opt S') "[Hskip #Hmatch]". iModIntro.
      iExists S', (case_map m k v t).
      iFrame "Hskip". iIntros "Hskip".
      iRight. iExists (m !! k). iSplitR "".
      { iSplit; last done. iExists head, S'; by iFrame "# ∗". }
      iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "Hres". iModIntro.
      wp_pures. case_match.
      + iDestruct "Hmatch" as "[-> _]". rewrite difference_empty_L.
        iApply "HΦ". by iIntros.
      + iDestruct "Hmatch" as (n new) "(Hopt & #Hn & _)".
        iDestruct ("Hres" with "Hopt") as (new') "(#Hn' & <- & Hsub & _)".
        iDestruct (mapsto_agree with "Hn Hn'") as %<-%rep_to_node_inj.
        iDestruct "Hopt" as %->. rewrite difference_empty_L.
        iApply "HΦ". iIntros. iExists new. by iFrame.
    Qed.

    Theorem put_spec (p: loc) (k v t: Z) (mΓ: gmap Z lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<< ∀∀ m, vc_map p m mΓ >>>
        put #p #k #v #t @ ∅
      <<< vc_map p (case_map m k v t) mΓ, RET #() >>>
      {{{ emp }}}.
    Proof.
      iIntros (Φ) "AU". pose proof HMAX_HEIGHT.
      wp_lam; wp_pures; wp_lam; wp_pures.
      awp_apply (putH_spec); try lia.
      iApply (aacc_aupd_eq with "AU"); try done.
      iIntros (m) "Hmap"; iAaccIntro with "Hmap".
      { iIntros; iModIntro; iFrame; by iIntros. }
      iIntros (?) "[Hmap _ ]". iModIntro.
      iExists (case_map m k v t).
      iFrame "Hmap". iIntros "Hmap".
      iRight. iFrame "Hmap". iIntros "AP".
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "_". by iApply "HΦ".
    Qed.
  End Proofs.
End PutSpec.