From SkipList.lazy_list Require Import inv.

From SkipList.lib Require Import lock.


Local Open Scope Z.
Module LazyListSpec (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Invariant := LazyListInv Params.
  Import Invariant.

  Section Proofs.
    Context `{!heapGS Σ, lockG Σ} (N : namespace).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ v, RET v; 
        is_lazy_list N ∅ v 
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".
      wp_lam. wp_alloc t as "Ht". wp_let.
      iDestruct "Ht" as "(Ht1&Ht2)".
      wp_apply ((newlock_spec (t ↦{#1 / 2} rep_to_node tail))%I with "[Ht1]").
      { iFrame. }
      iIntros (l) "#Hlock". iDestruct "Hlock" as (γ) "Hlock".
      set (head := (INT_MIN, Some t, l)).
      wp_pures; rewrite (fold_rep_to_node head).
      iMod (inv_alloc N ⊤ (lazy_list_inv ∅ head) with "[Ht2 Hlock]") as "Hinv".
      + iNext. iExists nil.
        iSplit. done. iSplit. simpl. 
        assert (node_lt head tail) as Hlt.
        { unfold node_lt; unfold node_key; simpl; apply HMIN_MAX. }
        auto using Hlt.
        iExists t, γ. iFrame "#". by iFrame.
      + iApply "HΦ". iExists head, ∅. iModIntro.
        iSplit. by unfold key_equiv.
        by (repeat iSplit).
    Qed.
    
    Theorem find_spec (head curr: node_rep) (key: Z) (S: gset node_rep) :
      {{{ 
        inv N (lazy_list_inv S head)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        ⌜ pred = head ∨ pred ∈ S ⌝
        ∗
        ⌜ succ ∈ S ∨ succ = tail ⌝
        ∗
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
        ∗
        ∃ (succ': node_rep) (l: loc) (γ: gname), ⌜ node_next pred = Some l ⌝ 
                                                 ∗ 
                                                 ⌜ succ' ∈ S ∨ succ' = tail ⌝
                                                 ∗ 
                                                 is_lock γ (node_lock pred) (l ↦{#1 / 2} (rep_to_node succ'))
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hcurr_range & Hrange) HΦ".
      iRevert (curr) "Hcurr_range Hrange HΦ".
      iLöb as "IH". 
      iIntros (curr) "%Hcurr_range %Hrange HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.

      destruct (node_next curr) as [l|] eqn:Hcurr_next; wp_pures.
      + wp_bind (Load _).
        iInv N as (L) "(>%Hperm & >%Hsort & Hlist)" "Hclose".

        edestruct (in_split curr ([head] ++ L)) as (Ls&Lf&Hcurr).
        { destruct Hcurr_range; first by left.
          right. apply elem_of_list_In. rewrite Hperm. apply elem_of_elements; auto. }
  
        edestruct (node_rep_split_join Lf curr key) as (pred&succ&L1&L2&?&Hsplit_join).
        { split; lia. }
  
        feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ key) as Htemp; eauto; try lia.
        destruct Htemp as [Lm Hsplit_sep].

        destruct Lm as [|next Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          iModIntro. wp_let. wp_lam. wp_pures.

          case_bool_decide; last lia.
          wp_pures. iApply "HΦ".
          iModIntro.

          iSplit; first by (iPureIntro; lia).
          iSplit; first by (iPureIntro; auto).
          iSplit.
          { 
            iPureIntro. rewrite -elem_of_elements. rewrite -Hperm.
            rewrite elem_of_list_In. apply in_inv_rev.
            destruct Ls.
            ++ inversion Hsplit_sep. by left.
            ++ inversion Hsplit_sep. apply in_app_iff.
               right. right; left. auto.
          }

          iSplit; last first.
          { 
            iExists succ, l, γ. iFrame "#". 
            iSplit. done.
            iPureIntro. rewrite -elem_of_elements. rewrite -Hperm.
            rewrite elem_of_list_In. apply in_inv_rev.
            destruct Ls.
            ++ inversion Hsplit_sep. by left.
            ++ inversion Hsplit_sep. apply in_app_iff.
               right. right; left. auto.
          }

          iPureIntro.
          rewrite -Hperm. split; intros.
          * eapply (sorted_node_lt_cover_gap (Ls ++ L1) L2 pred); try lia.
            ++ by rewrite app_ass -Hsplit_join //= app_comm_cons -app_ass -Hcurr app_ass.
            ++ cut (In key (map node_key ([head] ++ L ++ [tail]))).
               -- intros Hin. 
                  rewrite -app_ass Hcurr app_ass in Hin.
                  by rewrite app_ass -Hsplit_join.
               -- rewrite -app_ass map_app.
                  apply in_app_iff. left. right. 
                  by apply elem_of_list_In.
          * apply elem_of_list_In. apply in_map_iff. exists succ; split; auto.
            cut (In succ Lf).
            { 
              destruct Ls; inversion Hcurr; subst; auto.
              intros. rewrite in_app_iff. right. by right.
            }
            cut (In succ (Lf ++ [tail])).
            { 
              rewrite /tail.
              rewrite ?in_app_iff. intros [|[|[]]]; auto; subst. 
              unfold node_key in Hrange. simpl in Hrange. lia.
            }

            destruct L1.
            ** rewrite //= in Hsplit_join. inversion Hsplit_join as [[Heq1 Heq2]]; subst.
              rewrite Heq2. by left.
            ** inversion Hsplit_join as [[Heq1 Heq2]]; subst. rewrite Heq2.
              rewrite in_app_iff. right. right. left. auto.
        - rewrite (list_equiv_split curr next ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.
          wp_load.
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          iModIntro. wp_let. wp_lam. wp_pures.

          case_bool_decide as Hcase.
          * exfalso.
            cut (node_key next <= node_key pred); first by lia.
            assert (In pred (next :: Lm)) as Hpred_in_m.
            {
              symmetry in Hsplit_sep.
              rewrite Hsplit_sep //= in Hsort.
              rewrite //= app_comm_cons in Hsplit_join.
              rewrite -app_ass Hcurr app_ass Hsplit_join //= in Hsplit_sep.
              apply sorted_node_lt_no_dup in Hsort.

              destruct Lm as [|next' Lm] using rev_ind.
              -- left. eapply (no_dup_pred_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                 { apply NoDup_ListNoDup. rewrite app_ass //=. }
                 rewrite app_ass //= app_ass //=.
              -- right. apply in_app_iff. right. left.
                 eapply (no_dup_pred_unique (Ls ++ [curr; next] ++ Lm) L2 (Ls ++ L1) L2 succ).
                 { apply NoDup_ListNoDup. rewrite app_ass //= in Hsort. rewrite app_ass //=. }
                 rewrite app_ass //= in Hsplit_sep.
                 rewrite //= app_ass app_ass //=.
            }
            cut (Sorted node_lt ([next] ++ Lm)).
            -- intros Hsort'.
               apply Sorted_StronglySorted in Hsort'; last first.
               { unfold Relations_1.Transitive; apply node_lt_transitive. } 
               inversion Hsort'; subst. 
               inversion Hpred_in_m; first by (subst; lia).
               apply node_lt_le_incl.
               eapply Forall_forall; eauto.
               rewrite elem_of_list_In //=.
            -- rewrite -Hsplit_sep in Hsort.
               by repeat (apply node_rep_sorted_app in Hsort as (? & Hsort)).
          * wp_if.
            iApply ("IH" $! next with "[%] [%]").
            { 
              right. apply elem_of_elements. rewrite -Hperm.
              destruct Ls; assert (In next (L ++ [tail])) as Hin.
              -- inversion Hsplit_sep. by left.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst. exfalso. rewrite /node_key/tail//= in Hcase; lia.
              -- inversion Hsplit_sep. apply in_app_iff.
                 right. right; left. auto.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst. exfalso. rewrite /node_key/tail//= in Hcase; lia.
            }
            { lia. }

            iNext. iApply "HΦ".
      + iInv N as (L) "(>%Hperm & >%Hsort & Hlist)" "Hclose".

        edestruct (in_split curr ([head] ++ L)) as (Ls&Lf&Hcurr).
        { destruct Hcurr_range; first by left.
          right. apply elem_of_list_In. rewrite Hperm. apply elem_of_elements; auto. }
  
        edestruct (node_rep_split_join Lf curr key) as (pred&succ&L1&L2&?&Hsplit_join).
        { split; lia. }
  
        feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ key) as Htemp; eauto; try lia.
        destruct Htemp as [Lm Hsplit_sep].

        destruct Lm as [|next Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (? ?) "(>%Hsome & Hpt & #Hlock & Himp)".
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          congruence.
        - rewrite (list_equiv_split curr next ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (? ?) "(>%Hsome & Hpt & #Hlock & Himp)".
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          congruence.
    Qed.
    
    Theorem contains_spec (v: val) (key: Z) (Skeys: gset Z)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list N Skeys v }}}
        contains v #key
      {{{ (b: bool), RET #b; 
        is_lazy_list N Skeys v
        ∗
        ⌜ if b then key ∈ Skeys else key ∉ Skeys ⌝
      }}}.
    Proof.
      iIntros (Φ) "#H HΦ".
      iDestruct "H" as (head S) "(%Hequiv & %Hv & %Hmin & Hinv)".
      wp_lam. wp_let. rewrite -Hv.
      wp_apply (find_spec head head key S).
      { iSplit. done. iSplit. by iLeft. iPureIntro. lia. }
      iIntros (pred succ) "(%Hrange' & %Hpred_in_S & %Hsucc_in_S & %Hkey_in_S & Hlock)".
      wp_let. wp_match. wp_pures. wp_lam. wp_pures.
      iModIntro.

      case_bool_decide.
      + iApply "HΦ". iSplit. 
        iExists head, S. by iFrame "#".
        iPureIntro. unfold key_equiv in Hequiv. 
        apply elem_of_elements. rewrite Hequiv.
        apply Hkey_in_S. congruence.
      + iApply "HΦ". iSplit. 
        iExists head, S. by iFrame "#".
        iPureIntro. intros Hin. 
        apply elem_of_elements in Hin.
        rewrite Hequiv in Hin. apply Hkey_in_S in Hin.
        congruence.
    Qed.

    Theorem findLock_spec (head curr: node_rep) (key: Z) (S: gset node_rep) :
      {{{ 
        inv N (lazy_list_inv S head)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
      findLock (rep_to_node curr) #key
      {{{ pred succ, RET ((rep_to_node pred), (rep_to_node succ));
        ⌜ node_key pred < key ≤ node_key succ ⌝
        ∗
        ⌜ pred = head ∨ pred ∈ S ⌝
        ∗
        ⌜ succ ∈ S ∨ succ = tail ⌝
        ∗
        ∃ (l: loc) (γ: gname), ⌜ node_next pred = Some l ⌝
                               ∗
                               is_lock γ (node_lock pred) (l ↦{#1 / 2} (rep_to_node succ))
                               ∗
                               l ↦{#1 / 2} (rep_to_node succ)
                               ∗
                               locked γ
      }}}.
    Proof.
      iIntros (Φ) "(#Hinv & Hcurr_range & Hrange) HΦ".
      iRevert (curr) "Hcurr_range Hrange".
      iLöb as "IH". 
      iIntros (curr) "%Hcurr_range %Hrange".
      wp_lam. wp_let.
      wp_apply (find_spec head curr key S).
      {  by iFrame "#". }
      iIntros (pred succ) "(%Hrange' & %Hpred_in_S & %Hsucc_in_S & %Hkey_in_S & Hlock)".
      iDestruct "Hlock" as (succ' l γ) "(%Hsome & %Hsucc'_in_S & #Hlock)".
      wp_pures. wp_lam.
      wp_bind (Snd _).
      iInv N as (L) "(>%Hperm & >%Hsort & Hlist)" "Hclose".
      wp_pures.
      iMod ("Hclose" with "[Hlist]").
      { iNext. iExists L. by repeat iSplit. }
      iModIntro.
      wp_bind (acquire _).
      iApply (acquire_spec with "Hlock"); first done.
      iNext. iIntros (v) "(Hpt & Hlocked)".
      wp_pures. wp_lam. wp_pures.
      rewrite Hsome. wp_match.
      wp_load. wp_let. repeat (wp_lam; wp_pures).
      case_bool_decide as Heq; wp_if.
      + wp_pures.  iApply "HΦ". iModIntro.
        iSplit. done. iSplit. done. iSplit. done.
        iExists l, γ. iSplit. done.
        assert (succ = succ') as <-.
        {
          rewrite -elem_of_elements -Hperm elem_of_list_In -in_inv_rev in Hsucc_in_S.
          rewrite -elem_of_elements -Hperm elem_of_list_In -in_inv_rev in Hsucc'_in_S.
          apply (sorted_node_key_unique (L ++ [tail])); auto; last congruence.
          apply node_rep_sorted_app in Hsort; destruct Hsort; auto.
        }
        iFrame. iFrame "#".
      + wp_lam. wp_pures.
        wp_apply (release_spec with "[Hpt Hlocked]"); first done.
        { iFrame. by iSplit. }
        iIntros. wp_pures.
        iApply ("IH" with "HΦ"); auto.
    Qed.

  End Proofs.
End LazyListSpec.