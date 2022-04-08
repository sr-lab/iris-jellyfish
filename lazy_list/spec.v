From Coq Require Import Sorting.Sorted.

From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc lemmas.


Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Import Code.
  Module Lemmas := LazylistLemmas Params.
  Import Lemmas.

  Section Proofs.
    Context `{!heapGS Σ} (N : namespace).

    Fixpoint list_equiv (L: list node_rep) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (l: loc), 
                 ⌜ node_next pred = Some l ⌝
                 ∗
                 l ↦ rep_to_node tail

        | succ :: t => ∃ (l: loc), 
                       ⌜ node_next pred = Some l ⌝
                       ∗
                       l ↦ rep_to_node succ
                       ∗
                       list_equiv succs
        end
      end.

    Lemma list_equiv_cons (rep: node_rep) (L: list node_rep) :
      list_equiv (rep :: L)
        ⊢ (list_equiv L ∗ (list_equiv L -∗ list_equiv (rep :: L)))
    .
    Proof.
      destruct L as [|n].
      * iIntros "Hrep". by iFrame.
      * iIntros "Hlist". iDestruct "Hlist" as (l) "(Hsome & Hpt & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists l. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep):
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L ⊢ ∃ (l: loc),
                       ⌜ node_next pred = Some l ⌝
                       ∗
                       l ↦ (rep_to_node succ)
                       ∗
                       (l ↦ (rep_to_node succ) -∗ list_equiv L)
    .
    Proof.
      revert L. induction L1 => L HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (l) "(#Hsome & Hpt)".
          iExists l. iFrame "#"; iFrame.
          iIntros "Hpt". 
          iExists l. iFrame "#"; iFrame.
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (l) "(#Hsome & Hpt & Hmatch)".
          iExists l. iFrame "#"; iFrame.
          iIntros "Hpt". 
          iExists l. iFrame "#"; iFrame.
      + destruct L as [|curr L].
        { 
          exfalso. inversion HL  as [[H0 HL']]; subst. 
          destruct L1; inversion HL'.
        }
        inversion HL as [[H0 HL']]; subst.

        destruct L as [|curr L].
        { 
          exfalso. 
          destruct L1; inversion HL. 
          destruct L1; inversion HL.
        }
        
        iIntros "Hlist".
        iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof (IHL1 with "Hlist") as "Hlist"; auto.
        iDestruct "Hlist" as (l) "(Hsome & Hpt & Himp')".
        iExists l. iFrame. iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.
    
    (* 
    * The invariant for the lazy list asserts that
    * the underlying set S is sorted and must contain
    * the same elements as S.
    *)
    Definition lazy_list_inv (S: gset node_rep) (head: node_rep) : iProp Σ := 
      ∃ (L: list node_rep),
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      list_equiv ([head] ++ L)
    .

    (* 
    * Asserts that v points to a heap cell that 
    * represents the set S as a lazy list.
    *)
    Definition is_lazy_list (S: gset node_rep) (head: node_rep) : iProp Σ := 
      inv N (lazy_list_inv S head).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ (rep: node_rep), RET rep_to_node rep; 
        is_lazy_list ∅ rep 
      }}}.
    Proof.
      iIntros (Φ) "_ HΦ".
      wp_lam. wp_alloc t as "Ht". wp_pures.
      set (head := (INT_MIN, Some t, false, dummy_lock)).
      rewrite (fold_rep_to_node head).
      iMod (inv_alloc N ⊤ (lazy_list_inv ∅ head) with "[Ht]") as "Hinv".
      + iNext. iExists nil.
        iSplit. done. iSplit. simpl. 
        assert (node_lt head tail) as Hlt.
        { unfold node_lt; unfold node_key; simpl; apply HMIN_MAX. }
        auto using Hlt.
        iExists t. by iFrame.
      + by iApply "HΦ".
    Qed.
    
    Theorem find_spec (head curr: node_rep) (key: Z) (S: gset node_rep) :
      key < INT_MAX →
      {{{ 
        is_lazy_list S head 
        ∗
        ⌜ curr = head ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ succ, RET SOMEV (rep_to_node succ);
        is_lazy_list S head
        ∗
        ⌜ key ∈ map node_key (elements S) ↔ node_key succ = key ⌝
      }}}.
    Proof.
      intros Hrange.
      iIntros (Φ) "(#Hinv & Hcurr_range & Hcurr_key) HΦ".
      iRevert (curr) "Hcurr_range Hcurr_key HΦ".
      iLöb as "IH". 
      iIntros (curr) "%Hcurr_range %Hcurr_key HΦ".
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
          iDestruct "Hlist" as (l') "(>%Hsome & Hpt & Himp)".
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
          iSplit. done.

          iPureIntro. rewrite -Hperm. split; intros.
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
          iDestruct "Hlist" as (l') "(>%Hsome & Hpt & Himp)".
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
              apply sorted_node_lt_NoDup in Hsort.

              destruct Lm as [|next' Lm] using rev_ind.
              -- left. eapply (NoDup_pred_unique (Ls ++ [curr]) L2 (Ls ++ L1) L2 succ).
                 { apply NoDup_ListNoDup. rewrite app_ass //=. }
                 rewrite app_ass //= app_ass //=.
              -- right. apply in_app_iff. right. left.
                 eapply (NoDup_pred_unique (Ls ++ [curr; next] ++ Lm) L2 (Ls ++ L1) L2 succ).
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
              destruct Ls; assert (next ∈ L ++ [tail]) as Hin.
              -- inversion Hsplit_sep; subst; by left.
              -- apply elem_of_list_In, in_app_iff in Hin.
                 destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
                 subst. exfalso. rewrite /node_key/tail//= in Hcase; lia.
              -- inversion Hsplit_sep; subst.
                 apply elem_of_list_In. apply in_app_iff.
                 right. right; left. auto.
              -- apply elem_of_list_In, in_app_iff in Hin.
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
          iDestruct "Hlist" as (?) "(>%Hsome & Hpt & Himp)".
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
          iDestruct "Hlist" as (?) "(>%Hsome & Hpt & Himp)".
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          congruence.
    Qed.
    
    Theorem contains_spec (head: node_rep) (key: Z) (S: gset node_rep)
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list S head }}}
        contains (rep_to_node head) #key
      {{{ (b: bool), RET #b; 
        is_lazy_list S head
        ∗
        ⌜ if b then key ∈ (map node_key (elements S)) else key ∉ (map node_key (elements S)) ⌝
      }}}.
    Proof.
    Admitted.
  End Proofs.
End LazyListSpec.