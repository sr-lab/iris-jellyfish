From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.heap_lang Require Import notation.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import weakestpre proofmode lock.
From SkipList.jelly_fish Require Import code inv.
From SkipList.jelly_fish.spec Require Import find.


Module InsertSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Find := FindSpec Params.
  Export Find.

  Definition case_map (m: gmap Z (tval * list tval)) (k v t: Z) : gmap Z (tval * list tval) :=
    match m !! k with
    | None => <[k := (v, t, nil)]> m
    | Some (vt, vl) => if decide (Z.lt t vt.2) then m
                       else <[k := (v, t, vt :: vl)]> m
    end.

  Section Proofs.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    Theorem insert_spec (head curr new: node_rep) (n: loc)
      (Γ γ: lazy_gname) (lvl: Z) :
      0 < lvl →
      node_key head < node_key new < INT_MAX →
      node_key curr < node_key new →
      (⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[ curr ]})) -∗
      n ↦□ rep_to_node new -∗
      (node_next new +ₗ lvl) ↦ #() -∗
      (node_lock new +ₗ lvl) ↦ #false -∗
      has_sub γ new -∗
      <<< ∀∀ (S: gset node_rep), lazy_list head S Γ (Some γ) lvl >>>
        insert (rep_to_node curr) #lvl #n @ ∅
      <<< lazy_list head (S ∪ {[ new ]}) Γ (Some γ) lvl, RET #() >>>
      {{{
        has_sub Γ new
      }}}.
    Proof.
      iIntros "%Hlvl %Hk %Hk' #Hcurr #Hn Hnew Hlock [Hfrag' Htok'] %Φ AU".
      wp_lam; wp_pures. wp_load. wp_lam; wp_pures.

      awp_apply (findLock_spec with "Hcurr"); first lia.
      iApply (aacc_aupd_eq with "AU"); try done.
      iIntros (S) "Hlazy"; iAaccIntro with "Hlazy".
      { iIntros; iModIntro; iFrame; by iIntros. }
      iIntros (pred succ) "[Hlazy %Hnin]".
      iModIntro. iExists S. iFrame "Hlazy". iIntros "Hlazy".
      iLeft. iFrame "Hlazy". iIntros "AU". clear dependent S.
      iModIntro. iIntros "(#Hpred & #Hsucc & %Hk'' & Hacq)".
      iDestruct "Hacq" as (s) "(Hpt & #Hs & _ & Hacq)".
      iModIntro. wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.
      wp_load. wp_load. wp_lam; wp_pures.
      wp_store. iDestruct "Hnew" as "[Hnew Hnew']".
      wp_lam; wp_pures.

      wp_bind (Store _ _). iMod "AU" as (S) "[Hlazy [_ Hclose]]".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".

      iAssert ⌜ node_key new ≠ node_key succ ⌝%I as %Hneq.
      {
        iDestruct "Hsucc" as "[->|Hsucc]"; first (iPureIntro;
          rewrite /tail{2}/node_key/=; rewrite /tail{4}/node_key/= in Hk''; lia). 
        iDestruct (own_valid_2 with "Hauth Hsucc") 
          as %[Hvalid%gset_included]%auth_both_valid_discrete.
        rewrite (big_sepS_delete (has_sub _) _ succ); last set_solver.
        iDestruct "Hsubs" as "[[Hfrag Htok] Hsubs]".
        iDestruct (own_valid_2 with "Htok Htok'") as 
          %Hdisj%auth_frag_op_valid_1%gset_disj_valid_op.
        iPureIntro; set_solver.
      }

      rewrite (big_sepS_delete (has_next _ _) _ pred) //.
      iDestruct "Hnexts" as "[Hnext Hnexts]".
      iDestruct "Hnext" as (s' succ') "(Hnext & #Hs' & _ & Hkeys)".
      iDestruct (mapsto_agree with "Hpt Hnext") as %Hs; 
        symmetry in Hs; inversion Hs; subst; clear Hs.
      iDestruct (mapsto_agree with "Hs Hs'") as %<-%rep_to_node_inj.
      iClear "Hs'"; iCombine "Hpt Hnext" as "Hpt".
      wp_store. iDestruct "Hpt" as "[Hpt Hnext]".

      iMod (own_update with "Hauth") as "[Hauth Hfrag]".
      { by apply auth_update_alloc, (op_local_update_discrete _ _ {[new]}). }
      rewrite right_id (comm_L _ {[new]}). iDestruct "Hfrag" as "#Hfrag".

      rewrite (ZRange_split (node_key new)); last lia.
      iDestruct "Hkeys" as "((Hkeys & Hkey) & Hkeys')".
      iDestruct (own_valid_2 with "Hsort Hkey") as %Hdisj%gset_disj_valid_op.
      iCombine "Hsort Hkey" as "Hsort"; rewrite gset_disj_union //.

      iMod (own_update with "Htoks") as "[Htoks Htok]".
      { by apply auth_update_alloc, (gset_disj_alloc_op_local_update _ _ {[ node_key new ]}). }
      rewrite ?gset_disj_union // right_id_L (comm_L _ {[ node_key new ]}).

      iMod ("Hclose" with "[- Hpt Htok Hacq]") as "AP".
      { 
        rewrite /lazy_list set_map_union_L set_map_singleton_L; iFrame.
        assert (node_key new ≠ node_key head) by lia.
        iSplitL "Hnexts Hnext Hnew Hfrag Hkeys Hkeys'"; 
          last iSplitL "Hlocks Hlock Hnew'".
        + rewrite assoc_L (comm_L _ _ {[new]}).
          iApply big_sepS_insert; first set_solver.
          iSplitL "Hnew Hkeys'"; first (iExists s, succ; iFrame "# ∗").
          iApply big_sepS_delete; first done.
          iFrame. iExists n, new; iFrame "# ∗".
        + rewrite assoc_L (comm_L _ _ {[new]}).
          iApply big_sepS_insert; first set_solver.
          iFrame. iExists Free, (node_lock new +ₗ lvl).
          iSplit; first done. iFrame. iExists s; iFrame.
          by unfold locked_val; case_match; first lia.
        + rewrite comm_L big_sepS_insert; last set_solver. iFrame.
      }
      iModIntro. wp_pures.

      clear dependent S.
      iAssert (in_lock lvl pred)%I with "[Hpt]" as "Hin_lock". 
      { iExists n; iFrame "Hpt". by unfold locked_val; case_match; first lia. }
      awp_apply (release_spec with "Hacq Hin_lock").
      iApply (aacc_apst_sub with "[] AP"); try done.
      { 
        iIntros "!> %S H". iDestruct (node_has_lock with "Hpred H") as "[Hlock Hlazy]".
        iDestruct "Hlock" as (st) "Hlock". iExists st. iFrame. iIntros "Hlock".
        iApply "Hlazy". by iExists st. 
      }
      iIntros (S) "Hlazy".
      iDestruct (node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
      iDestruct "Hlock" as (st) "Hlock"; iAaccIntro with "Hlock".
      { 
        iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists st.
        iModIntro; iFrame; by iIntros.
      }
      iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
      iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists Free.
      iFrame "Hlazy". clear dependent S. iIntros "AP". rewrite difference_empty_L.
      iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "_". iApply "HΦ". iFrame "# ∗".
    Qed.

    Theorem tryInsert_spec (k v t h: Z) (head curr: node_rep) (Γ: lazy_gname) :
      node_key head < k < INT_MAX →
      node_key curr < k →
      0 ≤ h →
      (⌜ curr = head ⌝ ∨ own Γ.(auth_gname) (◯ {[ curr ]})) -∗
      <<< ∀∀ S m, jf_map head S m Γ >>>
        tryInsert (rep_to_node curr) #k #v #t #h @ ∅
      <<< ∃∃ opt S',
        jf_map head S' (case_map m k v t) Γ
        ∗
        match m !! k with 
        | None => ∃ (n: loc) (new: node_rep),
                    ⌜ opt = SOMEV #n ⌝ ∗ n ↦□ rep_to_node new ∗ ⌜ S' = S ∪ {[ new ]} ⌝
        | Some _ => ⌜ opt = NONEV ⌝ ∗ ⌜ S' = S ⌝
        end,
      RET opt >>>
      {{{
        ∀ (n: loc), ⌜ opt = SOMEV #n ⌝ -∗ ∃ (new: node_rep),
          n ↦□ rep_to_node new ∗ ⌜ node_key new = k ⌝ ∗ has_sub Γ new
          ∗
          (node_next new +ₗ 1) ↦∗ replicate (Z.to_nat h) #()
          ∗
          (node_lock new +ₗ 1) ↦∗ replicate (Z.to_nat h) #false
      }}}.
    Proof.
      iIntros "%Hk %Hk' %Hh #Hcurr %Φ AU".
      wp_lam; wp_pures.

      awp_apply (findLock_spec with "Hcurr"); first lia.
      iApply (aacc_aupd_sub with "[] AU"); try done.
      { iIntros "!> %S %m [H Hmap]". iExists S. iFrame "H". iIntros. iFrame. }
      iIntros (S m) "[Hlazy Hmap]"; iAaccIntro with "Hlazy".
      { iIntros; iModIntro; iFrame; by iIntros. }
      iIntros (pred succ) "[Hlazy %Hnin]".
      iModIntro. iExists S. iFrame "Hlazy". iIntros "Hlazy".
      iLeft. iFrame "Hlazy Hmap". iIntros "AU". clear dependent S m.
      iModIntro. iIntros "(#Hpred & #Hsucc & %Hk'' & Hacq)".
      iDestruct "Hacq" as (s) "(Hpt & #Hs & Hval & Hacq)".
      iDestruct "Hval" as (?) "[Hs' Hsucc']".
      iDestruct (mapsto_agree with "Hs Hs'") as %<-%rep_to_node_inj; iClear "Hs'".
      iModIntro. wp_pures; wp_lam; wp_pures; wp_lam; wp_pures.

      case_bool_decide as Hcase; wp_if.
      + assert (k = node_key succ) as Heq by congruence.
        iDestruct "Hsucc" as "[->|Hsucc]".
        { rewrite /node_key/tail/= in Heq; lia. }
        iDestruct "Hsucc'" as "[->|Hsucc']".
        { rewrite /node_key/tail/= in Heq; lia. }
        iDestruct "Hsucc'" as (val) "Hvpt".
        wp_lam; wp_pures; wp_lam; wp_pures.

        (* We start the case analysis here, since it's easier to use the load
        operation as the linearisation point for when no update occurs. *)
        destruct (decide (t < (val_vt val).2)) as [Ht|Ht].
        - (* The key already exists with a more recent timestamp*)
          wp_bind (Load _). iMod "AU" as (S m) "[[Hlazy Hmap] [_ Hclose]]".
          iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & _)".
          iDestruct (own_valid_2 with "Hauth Hsucc") 
            as %[?%gset_included]%auth_both_valid_discrete.
          iDestruct "Hmap" as (γ) "(%Hdom & Hgmap & Hvals)".
          rewrite (big_sepS_delete (has_val _) _ succ); last set_solver.
          iDestruct "Hvals" as "[Hval Hvals]".
          iDestruct "Hval" as (? vl) "(Hvpt' & Hkey & Hvl)".
          iDestruct (ghost_map_lookup with "Hgmap Hkey") as %Hsome; 
            rewrite -Heq in Hsome.
          iDestruct (mapsto_agree with "Hvpt Hvpt'") as %<-%rep_to_val_inj.

          wp_load. rewrite /case_map Hsome.
          case_decide as Hcase'; simpl in Hcase'; last lia.
          iMod ("Hclose" $! NONEV S with "[- Hpt Hvpt Hacq]") as "AP".
          {
            iSplit; last done. iFrame. iExists γ.
            iFrame "Hgmap". iSplit; first done.
            iApply (big_sepS_delete _ _ succ); first set_solver.
            iFrame "Hvals". iExists val, vl. iFrame.
          }
          iModIntro. wp_pures; wp_lam; wp_pures.
          case_bool_decide as Ht'; wp_if; last first.
          { unfold val_vt in Ht; unfold val_t in Ht'; lia. }
          wp_pures.

          clear dependent S m γ vl.
          iAssert (in_lock 0 pred)%I with "[Hpt Hvpt]" as "Hin_lock". 
          { iExists s; iFrame "Hpt". iExists succ; iFrame "Hs". iRight; by iExists val. }
          rewrite -{2}(Loc.add_0 (node_lock pred)).
          awp_apply (release_spec with "Hacq Hin_lock").
          iApply (aacc_apst_sub with "[] AP"); try done.
          { 
            iIntros "!> %S %m [H ?]". iDestruct (node_has_lock with "Hpred H") as "[Hlock Hlazy]".
            iDestruct "Hlock" as (st) "Hlock". iExists st. iFrame. iIntros "Hlock".
            iApply "Hlazy". by iExists st. 
          }
          iIntros (S m) "[Hlazy Hmap]".
          iDestruct (node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
          iDestruct "Hlock" as (st) "Hlock"; iAaccIntro with "Hlock".
          { 
            iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists st.
            iModIntro; iFrame; by iIntros.
          }
          iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
          iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists Free.
          iFrame "Hlazy Hmap". iIntros "AP". rewrite difference_empty_L.
          iMod (atomic_post_commit with "AP") as "HΦ".
          iModIntro. iIntros "_". iModIntro. wp_pures.
          iApply "HΦ". iIntros. congruence.
        - (* The key already exists but with an outdated timestamp *)
          wp_load. wp_pures; wp_lam; wp_pures.
          case_bool_decide as Ht'; wp_if.
          { unfold val_vt in Ht; unfold val_t in Ht'; lia. }

          wp_alloc prev as "Hprev". wp_pures; wp_lam; wp_pures.
          iMod (mapsto_persist with "Hprev") as "#Hprev".
          set (val' := (v, t, prev)).
          rewrite (fold_rep_to_val val').

          wp_bind (Store _ _). iMod "AU" as (S m) "[[Hlazy Hmap] [_ Hclose]]".
          iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & _)".
          iDestruct (own_valid_2 with "Hauth Hsucc") 
            as %[?%gset_included]%auth_both_valid_discrete.
          iDestruct "Hmap" as (γ) "(%Hdom & Hgmap & Hvals)".
          rewrite (big_sepS_delete (has_val _) _ succ); last set_solver.
          iDestruct "Hvals" as "[Hval Hvals]".
          iDestruct "Hval" as (? vl) "(Hvpt' & Hkey & Hvl)".
          iDestruct (ghost_map_lookup with "Hgmap Hkey") as %Hsome; 
            rewrite -Heq in Hsome.
          iDestruct (mapsto_agree with "Hvpt Hvpt'") as %<-%rep_to_val_inj.
          iCombine "Hvpt Hvpt'" as "Hvpt". wp_store.
          iDestruct "Hvpt" as "[Hvpt Hvpt']".

          iMod (ghost_map_update (v, t, val_vt val :: vl) with "Hgmap Hkey")
            as "[Hgmap Hkey]".

          rewrite /case_map Hsome Heq.
          case_decide as Hcase'; simpl in Hcase'; first lia.
          iMod ("Hclose" $! NONEV S with "[- Hpt Hvpt Hacq]") as "AP".
          {
            iSplit; last done. iFrame. iExists γ.
            iFrame "Hgmap". iSplit; first rewrite -Heq -Hdom dom_insert_lookup_L //.
            iApply (big_sepS_delete _ _ succ); first set_solver.
            iFrame "Hvals". iExists val', (val_vt val :: vl). iFrame.
            iExists (val_p val); iFrame "# ∗".
          }
          iModIntro. wp_pures.

          clear dependent S m γ vl.
          iAssert (in_lock 0 pred)%I with "[Hpt Hvpt]" as "Hin_lock". 
          { iExists s; iFrame "Hpt". iExists succ; iFrame "Hs". iRight; by iExists val'. }
          rewrite -{2}(Loc.add_0 (node_lock pred)).
          awp_apply (release_spec with "Hacq Hin_lock").
          iApply (aacc_apst_sub with "[] AP"); try done.
          { 
            iIntros "!> %S %m [H ?]". iDestruct (node_has_lock with "Hpred H") as "[Hlock Hlazy]".
            iDestruct "Hlock" as (st) "Hlock". iExists st. iFrame. iIntros "Hlock".
            iApply "Hlazy". by iExists st. 
          }
          iIntros (S m) "[Hlazy Hmap]".
          iDestruct (node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
          iDestruct "Hlock" as (st) "Hlock"; iAaccIntro with "Hlock".
          { 
            iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists st.
            iModIntro; iFrame; by iIntros.
          }
          iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
          iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists Free.
          iFrame "Hlazy Hmap". iIntros "AP". rewrite difference_empty_L.
          iMod (atomic_post_commit with "AP") as "HΦ".
          iModIntro. iIntros "_". iModIntro. wp_pures.
          iApply "HΦ". iIntros. congruence.
      + (* The key does not exists in the map *)
        assert (k ≠ node_key succ) by congruence.
        wp_lam; wp_pures.
        
        wp_alloc next as "Hnexts"; first lia. wp_let.
        wp_alloc lock as "Hlocks"; first lia. wp_let.
        assert (Z.to_nat (h + 1) = S (Z.to_nat h)) as -> by lia.
        rewrite ?replicate_S ?array_cons ?Loc.add_0.
        iDestruct "Hnexts" as "[Hnext Hns]".
        iDestruct "Hlocks" as "[Hlock Hls]".

        wp_alloc vpt as "[Hvpt Hvpt']". wp_let.
        wp_alloc n as "Hn". wp_let. iMod (mapsto_persist with "Hn") as "#Hn".
        set (val := (v, t, dummy_null)); set (new := (k, vpt, next, lock)).
        rewrite (fold_rep_to_val val) (fold_rep_to_node new).

        wp_lam; wp_pures. wp_load. wp_load. wp_lam; wp_pures.
        wp_store. iDestruct "Hnext" as "[Hnext Hnext']".
        wp_lam; wp_pures.

        wp_bind (Store _ _). iMod "AU" as (S m) "[[Hlazy Hmap] [_ Hclose]]".
        iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
        iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & _)".

        rewrite (big_sepS_delete (has_next _ _) _ pred) //.
        iDestruct "Hnexts" as "[Hpt' Hnexts]".
        iDestruct "Hpt'" as (s' succ') "(Hpt' & #Hs' & _ & Hkeys)".
        rewrite Loc.add_0.
        iDestruct (mapsto_agree with "Hpt Hpt'") as %Hs; 
          symmetry in Hs; inversion Hs; subst; clear Hs.
        iDestruct (mapsto_agree with "Hs Hs'") as %<-%rep_to_node_inj; iClear "Hs'".
        iCombine "Hpt Hpt'" as "Hpt".
        wp_store. iDestruct "Hpt" as "[Hpt Hpt']".

        iMod (own_update with "Hauth") as "[Hauth Hfrag]".
        { by apply auth_update_alloc, (op_local_update_discrete _ _ {[new]}). }
        rewrite right_id (comm_L _ {[new]}). iDestruct "Hfrag" as "#Hfrag".

        rewrite (ZRange_split (node_key new)); last first.
        { replace (node_key new) with k by auto; lia. }
        iDestruct "Hkeys" as "((Hkeys & Hkey) & Hkeys')".
        iDestruct (own_valid_2 with "Hsort Hkey") as %Hdisj%gset_disj_valid_op.
        iCombine "Hsort Hkey" as "Hsort"; rewrite gset_disj_union //.

        iMod (own_update with "Htoks") as "[Htoks Htok]".
        { by apply auth_update_alloc, (gset_disj_alloc_op_local_update _ _ {[ node_key new ]}). }
        rewrite ?gset_disj_union // right_id_L (comm_L _ {[ node_key new ]}).

        iDestruct "Hmap" as (γ) "(%Hdom & Hgmap & Hvals)".
        assert (m !! k = None) as Heq by (rewrite -not_elem_of_dom; set_solver).
        iMod (ghost_map_insert k (v, t, nil) with "Hgmap") as "[Hgmap Hval]"; 
          first done; rewrite /case_map Heq; clear Heq.

        rewrite -(Loc.add_0 (node_next pred)) -(Loc.add_0 (node_next new)).
        iMod ("Hclose" $! (SOMEV #n) (S ∪ {[ new ]}) with "[- Hpt Hvpt Hacq Hns Hls Htok]") as "AP".
        {
          iSplit; last (iExists n, new; by iFrame "Hn").
          iSplitR "Hvals Hvpt' Hgmap Hval".
          + rewrite /lazy_list set_map_union_L set_map_singleton_L; iFrame.
            assert (k ≠ node_key head) by lia.
            iSplitR "Hlock Hlocks Hnext' Hsucc'"; last (iSplit; last done).
            - rewrite assoc_L (comm_L _ ({[head]} ∪ S)).
              iApply big_sepS_insert; first set_solver.
              iSplitL "Hnext Hkeys'"; first (iExists s, succ; iFrame "# ∗").
              iApply big_sepS_delete; first done.
              iFrame "Hnexts". iExists n, new; iFrame "# ∗".
            - rewrite assoc_L (comm_L _ ({[head]} ∪ S)).
              iApply big_sepS_insert; first set_solver.
              iFrame "Hlocks". iExists Free, (node_lock new).
              iSplitL ""; first rewrite Loc.add_0 //.
              iFrame. iExists s; iFrame. iExists succ; iFrame "# ∗".
          + iExists γ. iFrame "Hgmap". iSplit; first iPureIntro.
            - rewrite set_map_union_L set_map_singleton_L -Hdom dom_insert_L comm_L //.
            - rewrite comm_L; iApply big_sepS_insert; first set_solver.
              iFrame "Hvals". iExists val, nil. by iFrame.
        }
        iModIntro. wp_pures.

        clear dependent S m γ.
        iAssert (in_lock 0 pred)%I with "[Hpt Hvpt]" as "Hin_lock". 
        { iExists n; iFrame "Hpt". iExists new. iFrame "Hn". iRight. by iExists val. }

        rewrite -(Loc.add_0 (node_lock pred)).
        awp_apply (release_spec with "Hacq Hin_lock").
        iApply (aacc_apst_sub with "[] AP"); try done.
        { 
          iIntros "!> %S %m [H ?]". iDestruct (node_has_lock with "Hpred H") as "[Hlock Hlazy]".
          iDestruct "Hlock" as (st) "Hlock". iExists st. iFrame. iIntros "Hlock".
          iApply "Hlazy". by iExists st. 
        }
        iIntros (S m) "[Hlazy Hmap]".
        iDestruct (node_has_lock with "Hpred Hlazy") as "[Hlock Hlazy]".
        iDestruct "Hlock" as (st) "Hlock"; iAaccIntro with "Hlock".
        { 
          iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists st.
          iModIntro; iFrame; by iIntros.
        }
        iIntros "Hlock"; iModIntro; iExists Free; iFrame "Hlock".
        iIntros "H"; iDestruct ("Hlazy" with "[H]") as "Hlazy"; first by iExists Free.
        iFrame "Hlazy Hmap". iIntros "AP". rewrite difference_empty_L.
        iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "_". iModIntro. wp_pures.
        iApply "HΦ". iIntros (n' ?); replace n' with n by congruence.
        iExists new. by iFrame "# ∗".
    Qed.
  End Proofs.
End InsertSpec.