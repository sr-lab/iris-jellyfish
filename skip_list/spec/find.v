From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_rep code key_equiv.
From SkipList.skip_list.inv Require Import skip_inv.


Local Open Scope Z.
Module FindSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Invariant := SkipListInv Params.
  Export Invariant.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).
    
    Theorem find_spec (head curr: node_rep) (key: Z) (S: gset node_rep) (P: node_rep -> iProp Σ) :
      {{{ 
        inv N (lazy_list_inv head S P)
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key < INT_MAX ⌝
      }}}
        find (rep_to_node curr) #key
      {{{ pred succ, RET SOMEV ((rep_to_node pred), (rep_to_node succ));
        ⌜ pred = head ∨ pred ∈ S ⌝
        ∗
        ⌜ node_key pred < key ⌝
        ∗
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
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

        edestruct (in_split curr ([head] ++ L)) 
          as (Ls&Lf&Hcurr).
        { 
          destruct Hcurr_range; first by left. 
          by right; rewrite -elem_of_list_In Hperm elem_of_elements. 
        }
  
        edestruct (node_rep_split_join Lf curr key) 
          as (pred&succ&L1&L2&?&Hsplit_join); auto.
  
        feed pose proof (node_rep_split_sep L Ls Lf L1 L2 head curr pred succ key) 
          as Htemp; auto.
        destruct Htemp as [Lm Hsplit_sep].

        destruct Lm as [|next Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp]") as "_".
          {
            iNext; iExists L.
            iPoseProof ("Himp" with "Hpt") as "Hlist".
            by iFrame.
          }

          iModIntro. wp_let. wp_lam. wp_pures.
          case_bool_decide; last lia.
          wp_pures. iApply "HΦ".
          iModIntro; iPureIntro.

          split; first done.
          split; first lia.
          rewrite -Hperm; split; intros.
          * eapply (sorted_node_lt_cover_gap (Ls ++ L1) L2 pred); try lia.
            ++ by rewrite app_ass -Hsplit_join //= app_comm_cons -app_ass -Hcurr app_ass.
            ++ assert (In key (map node_key ([head] ++ L ++ [tail]))) as Hin.
               { rewrite -app_ass map_app in_app_iff; left; right. 
                 by apply elem_of_list_In. }
               rewrite -app_ass Hcurr app_ass in Hin.
               by rewrite app_ass -Hsplit_join.
          * rewrite elem_of_list_In in_map_iff. exists succ; split; auto.
            cut (In succ Lf).
            { destruct Ls; inversion Hcurr; subst; auto.
              intros; by rewrite in_app_iff; right; right. }

            cut (In succ (Lf ++ [tail])).
            { rewrite /tail ?in_app_iff.
              intros [|[|[]]]; auto; subst. 
              rewrite /node_key /= in Hrange; lia. }

            destruct L1.
            ** rewrite //= in Hsplit_join. 
               inversion Hsplit_join as [[Heq1 Heq2]]; subst.
               by rewrite Heq2; left.
            ** inversion Hsplit_join as [[Heq1 Heq2]]; subst.
               by rewrite Heq2 in_app_iff; right; right; left.
        - rewrite (list_equiv_split curr next ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist" as (l' γ) "(>%Hsome & Hpt & #Hlock & Himp)".
          assert (l = l') as <- by congruence.

          wp_load.
          iMod ("Hclose" with "[Hpt Himp]") as "_".
          {
            iNext; iExists L.
            iPoseProof ("Himp" with "Hpt") as "Hlist".
            by iFrame.
          }

          iModIntro. wp_let. wp_lam. wp_pures.
          case_bool_decide as Hcase.
          * exfalso.
            assert (node_key next <= node_key pred); last by lia.

            assert (In pred (next :: Lm)) as Hpred_in_m.
            {
              symmetry in Hsplit_sep.
              rewrite Hsplit_sep //= in Hsort.
              rewrite //= app_comm_cons in Hsplit_join.
              rewrite -app_ass Hcurr app_ass Hsplit_join //= in Hsplit_sep.
              apply sorted_node_lt_no_dup in Hsort.

              destruct Lm as [|next' Lm] using rev_ind.
              -- left. eapply (no_dup_elem_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                 { rewrite app_ass //=. }
                 rewrite app_ass //= app_ass //=.
              -- right. apply in_app_iff. right. left.
                 eapply (no_dup_elem_unique (Ls ++ [curr; next] ++ Lm) L2 (Ls ++ L1) L2 succ).
                 { rewrite app_ass //= in Hsort. rewrite app_ass //=. }
                 rewrite app_ass //= in Hsplit_sep.
                 rewrite //= app_ass app_ass //=.
            }

            rewrite -Hsplit_sep in Hsort.
            do 2 apply node_rep_sorted_app in Hsort as (_ & Hsort).
            apply node_rep_sorted_app in Hsort as (Hsort & _).

            apply Sorted_StronglySorted in Hsort; last first.
            { unfold Relations_1.Transitive; apply node_lt_transitive. } 
            inversion Hsort; subst. 
            inversion Hpred_in_m; first by (subst; lia).
            eapply node_lt_le_incl, Forall_forall; eauto.
            rewrite elem_of_list_In //=.
          * wp_if.
            iApply ("IH" $! next with "[%] [%]").
            { 
              right. rewrite -elem_of_elements -Hperm.
              destruct Ls; assert (In next (L ++ [tail])) as Hin.
              -- inversion Hsplit_sep. by left.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst; exfalso. 
                 rewrite /node_key/tail//= in Hcase; lia.
              -- inversion Hsplit_sep. 
                 by apply in_app_iff; right; right; left.
              -- apply in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst; exfalso. 
                 rewrite /node_key/tail//= in Hcase; lia.
            }
            { lia. }

            iNext; iApply "HΦ".
      + iInv N as (L) "(>%Hperm & >%Hsort & Hlist)" "Hclose".

        rewrite list_equiv_invert; last by rewrite -elem_of_list_In Hperm elem_of_elements.
        iDestruct "Hlist" as (succ l γ) "(Hsucc_range & Hsome & Hpt & #Hlock & Himp)".
        iMod "Hsome" as %Hsome; congruence.
    Qed.

  End Proofs.
End FindSpec.