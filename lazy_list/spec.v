From Coq Require Import Sorting.Sorted.

From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc lemmas.


Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

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
      + destruct L as [| curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [| curr L].
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
      + destruct L as [| curr L].
        { 
          exfalso. inversion HL  as [[H0 HL']]; subst. 
          destruct L1; inversion HL'.
        }
        inversion HL as [[H0 HL']]; subst.

        destruct L as [| curr L].
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
    
    Theorem find_spec (head curr pred succ: node_rep) (key: Z)
      (S: gset node_rep) (L Li Lm Le: list node_rep) :
      Permutation (elements S) L →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      INT_MIN < key < INT_MAX →
      node_key pred < key <= node_key succ →
      Li ++ [curr] ++ Lm ++ [succ] ++ Le = [head] ++ L ++ [tail] →
      (∃ (L1 L2: list node_rep), L1 ++ [pred; succ] ++ L2 = [head] ++ L ++ [tail]) →
      {{{ 
        is_lazy_list S head 
        ∗
        ⌜ node_key curr = INT_MIN ∨ curr ∈ S ⌝
        ∗
        ⌜ node_key curr < key ⌝
      }}}
      find (rep_to_node curr) #key
      {{{ ocurr, RET ocurr;
        is_lazy_list S head
        ∗
        ⌜ ocurr = SOMEV (rep_to_node succ) ⌝
      }}}.
    Proof.
      intros Hperm Hsort Hrange Hkey Hsplit_sep Hsplit_join.
      iIntros (Φ) "(#Hinv & Hcurr_range & Hcurr_key) HΦ".
      iRevert (curr Li Lm Hsplit_sep) "Hcurr_range Hcurr_key HΦ".
      iLöb as "IH". 
      iIntros (curr Li Lm Hsplit_sep) "Hcurr_range Hcurr_key HΦ".
      wp_lam. wp_let. wp_lam. wp_pures.
      destruct (node_next curr) as [l|] eqn:Hcurr_next; wp_pures.
      + wp_bind (Load _).
        iInv N as (L') "(>%Hperm' & >%Hsort' & Hlist')" "Hclose".

        assert (L = L') as <-.
        {
          eapply node_rep_sorted_eq.
          * inversion Hsort as [| ? ? H]; subst.
            eapply node_rep_sorted_app in H. destruct H. done.
          * inversion Hsort' as [| ? ? H]; subst.
            eapply node_rep_sorted_app in H. destruct H. done.
          * by rewrite -Hperm.
        }

        destruct Lm as [|curr' Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist'" as (l'') "(>%Hsome & Hpt & Himp)".
          assert (l = l'') as <- by congruence.
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
          iModIntro. by iSplit.
        - rewrite (list_equiv_split curr curr' ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist'" as (l'') "(>%Hsome & Hpt & Himp)".
          assert (l = l'') as <- by congruence.
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
            cut (node_key curr' <= node_key pred); first by lia.
            assert (In pred (curr' :: Lm)) as Hpred_in_m.
            ++ destruct Hsplit_join as (L1 & L2 & Hsplit_join).
               rewrite -Hsplit_join in Hsplit_sep.
               induction Lm as [| curr'' Lm] using rev_ind.
               -- simpl in Hsplit_sep.
                  left. eapply (NoDup_pred_unique (Li ++ [curr])); rewrite app_ass //=.
                  rewrite Hsplit_sep. rewrite Hsplit_join.
                  rewrite -NoDup_ListNoDup. by apply sorted_node_lt_NoDup.
               -- right. apply in_app_iff. right.
                  rewrite //= in Hsplit_sep.
                  left. eapply (NoDup_pred_unique (Li ++ [curr; curr'] ++ Lm)); 
                    rewrite app_ass //= in Hsplit_sep; rewrite app_ass //=.
                  rewrite Hsplit_sep Hsplit_join.
                  rewrite -NoDup_ListNoDup. by apply sorted_node_lt_NoDup.
            ++ cut (Sorted node_lt ([curr'] ++ Lm)).
               -- intros Hsort''.
                  apply Sorted_StronglySorted in Hsort''; last first.
                  { unfold Relations_1.Transitive; apply node_lt_transitive. } 
                  inversion Hsort''; subst. 
                  inversion Hpred_in_m; first by (subst; lia).
                  apply node_lt_le_incl.
                  by eapply Forall_forall.
               -- rewrite -Hsplit_sep in Hsort.
                  by repeat (apply node_rep_sorted_app in Hsort as (? & Hsort)).
          * wp_if.
            iApply ("IH" $! curr' (Li ++ [curr]) Lm with "[%] [%] [%]").

            { rewrite app_ass //=. }
            { 
              right. apply elem_of_elements. rewrite Hperm.
              destruct Li; assert (curr' ∈ L ++ [tail]) as Hin.
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
      + iInv N as (L') "(>%Hperm' & >%Hsort' & Hlist')" "Hclose".
      
        assert (L = L') as <-.
        {
          eapply node_rep_sorted_eq.
          * inversion Hsort as [| ? ? H]; subst.
            eapply node_rep_sorted_app in H. destruct H. done.
          * inversion Hsort' as [| ? ? H]; subst.
            eapply node_rep_sorted_app in H. destruct H. done.
          * by rewrite -Hperm.
        }

        destruct Lm as [|curr' Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist'" as (l'') "(>%Hsome & Hpt & Himp)".
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          congruence.
        - rewrite (list_equiv_split curr curr' ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }
          iDestruct "Hlist'" as (l'') "(>%Hsome & Hpt & Himp)".
          iMod ("Hclose" with "[Hpt Himp]").
          {
            iNext. iExists L.
            iSplit. done.
            iSplit. done.
            iApply "Himp". iFrame.
          }
          congruence.
    Qed.

    (* Theorem contains_spec (S: gset Z) (v: val) (key: Z) 
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list S v }}}
        contains v #key
      {{{ b, RET b; 
        is_lazy_list S v
        ∗
        ⌜ (b = #false ∧ key ∉ S)
        ∨
        (b = #true ∧ key ∈ S) ⌝
      }}}.
    Proof.
    Admitted. *)
  End Proofs.
End LazyListSpec.