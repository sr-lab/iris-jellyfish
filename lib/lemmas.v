From Coq Require Import Lia Sorting.Sorted.

From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.


Local Open Scope Z.
Module LazylistLemmas (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

  Lemma node_lt_transitive :
    forall x y z, node_lt x y -> node_lt y z -> node_lt x z
  .
  Proof.
    intros x y z. unfold node_lt.
    intros xy yz. lia.
  Qed.

  Lemma node_lt_le_incl : 
    ∀ x y, node_lt x y → node_key x ≤ node_key y
  .
  Proof.
    intros x y Hlt.
    unfold node_lt in Hlt. lia.
  Qed.

  Lemma node_rep_sorted_eq (l l': list node_rep) :
    Sorted node_lt l →
    Sorted node_lt l' →
    Permutation l l' →
    l = l'.
  Proof.
    revert l'.
    induction l.
    - intros l' ?? ?%Permutation.Permutation_nil. subst. auto.
    - intros l' Hsorted Hsorted' Hperm.
      destruct l' as [| a' l'].
      { symmetry in Hperm. apply Permutation.Permutation_nil in Hperm. congruence. } 
      destruct_decide (decide (a = a')) as Hcase.
      { intros; subst.  f_equal.
        eapply IHl.
        { eapply Sorted_inv; eauto. }
        { eapply Sorted_inv; eauto. }
        apply Permutation.Permutation_cons_inv in Hperm; eauto.
      }
      
      exfalso. cut (node_key a < node_key a' ∧ node_key a' < node_key a); first lia.
      split.
      * apply Sorted_StronglySorted in Hsorted; last eauto with *.
        inversion Hsorted as [| ??? Hall]; subst.
        assert (List.In a' (a :: l)) as [|]; subst.
        { apply elem_of_list_In. rewrite Hperm. by left. }
        ** congruence. 
        ** eapply List.Forall_forall in Hall; eauto.
        ** unfold Relations_1.Transitive.
          apply node_lt_transitive.
      * apply Sorted_StronglySorted in Hsorted'; last eauto with *.
        inversion Hsorted' as [| ??? Hall]; subst.
        assert (List.In a (a' :: l')) as [|]; subst.
        { apply elem_of_list_In. rewrite -Hperm. by left. }
        ** congruence. 
        ** eapply List.Forall_forall in Hall; eauto.
        ** unfold Relations_1.Transitive.
          apply node_lt_transitive.
  Qed.

  Lemma StronglySorted_app {A: Type} R (L1 L2: list A) :
    StronglySorted R (L1 ++ L2) →
    StronglySorted R L1 ∧ StronglySorted R L2.
  Proof.
    induction L1.
    - rewrite //=; intros; intuition; econstructor.
    - intros Hs.
      inversion Hs; subst; eauto.
      edestruct IHL1; eauto. split; auto.
      econstructor; eauto.
      apply list.Forall_forall. intros. eapply list.Forall_forall; eauto.
      apply elem_of_list_In. apply in_or_app. left. apply elem_of_list_In; done.
  Qed.

  Lemma node_rep_sorted_app (L1 L2: list node_rep) :
    Sorted node_lt (L1 ++ L2) → Sorted node_lt L1 ∧ Sorted node_lt L2.
  Proof.
    intros HS. apply Sorted_StronglySorted in HS; last eauto with *.
    + apply StronglySorted_app in HS as (?&?); split; eauto using StronglySorted_Sorted.
    + unfold Relations_1.Transitive.
      apply node_lt_transitive.
  Qed.

  Lemma node_rep_split_join (L: list node_rep) (head: node_rep) (k: Z):
    node_key head < k < INT_MAX →
    ∃ (pred succ: node_rep) (L1 L2: list node_rep),
      node_key pred < k ≤ node_key succ ∧
      [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2.
  Proof.
    revert head.
    induction L as [| curr L] => head.
    - intros (?&?). exists head, tail, nil, nil.
      split_and!; auto. rewrite /tail/node_key//=; eauto. lia.
    - intros (?&?).
      destruct (Z_lt_dec (node_key curr) k).
      * edestruct IHL as (pred&succ&L1&L2&Hrange&Heq); eauto.
        destruct Hrange.
        exists pred, succ, (head :: L1), L2.
        split_and!;eauto. simpl in *. rewrite Heq. auto.
      * exists head, curr, nil, (L ++ [tail]).
        split_and!; eauto; lia.
  Qed.

  Lemma node_rep_split_sep (L Li Lf L1 Le: list node_rep) 
    (head curr pred succ: node_rep) (k: Z) :
    Sorted node_lt ([head] ++ L ++ [tail]) →
    node_key curr < k < INT_MAX →
    node_key pred < k ≤ node_key succ  →
    [head] ++ L = Li ++ [curr] ++ Lf →
    [curr] ++ Lf ++ [tail] = L1 ++ [pred; succ] ++ Le →
    ∃ (Lm: list node_rep), 
      Li ++ [curr] ++ Lm ++ [succ] ++ Le = [head] ++ L ++ [tail].
  Proof.
    intros Hsort Hr1 Hr2 Heq1 Heq2.
    destruct L1 as [| a L1].
    + exists nil. simpl in *.
      inversion Heq2. symmetry.
      rewrite app_comm_cons Heq1 app_ass.
      subst; auto.
    + inversion Heq2; subst.
      exists (L1 ++ [pred]). symmetry. 
      rewrite -app_ass Heq1 app_ass. f_equal.
      rewrite app_ass. f_equal.
      rewrite H1 app_ass //=.
  Qed.

  Lemma sorted_node_lt_Zlt (L: list node_rep) :
    Sorted node_lt L →
    Sorted Z.lt (map node_key L).
  Proof.
    induction 1 as [| ?? Hsorted IH Hhd]; econstructor; eauto.
    by inversion Hhd as [| ? ? Hhd']; subst; econstructor.
  Qed.

  Lemma strongly_sorted_node_lt_Zlt (L: list node_rep) :
    StronglySorted node_lt L →
    StronglySorted Z.lt (map node_key L).
  Proof.
    intros.
    apply StronglySorted_Sorted in H.
    apply Sorted_StronglySorted; eauto with *.
    by apply sorted_node_lt_Zlt.
  Qed.

  Lemma forall_node_lt_Zlt (L: list node_rep) (rep: node_rep) :
    Forall (node_lt rep) L →
    Forall (Z.lt (node_key rep)) (map node_key L).
  Proof.
    induction 1; econstructor; eauto.
  Qed.

  Lemma sorted_node_lt_cover_gap (L1 L2: list node_rep) (pred succ: node_rep) (k: Z):
    Sorted node_lt (L1 ++ [pred; succ] ++ L2) →
    node_key pred < k ≤ node_key succ →
    In k (map node_key (L1 ++ [pred; succ] ++ L2)) →
    node_key succ = k.
  Proof.
    induction L1.
    - rewrite //= => Hsort Hr Hin. inversion Hin as [|[Heq|Hin']]; subst; try lia.
      exfalso. apply Sorted_StronglySorted in Hsort; last first.
      { unfold Relations_1.Transitive; apply node_lt_transitive. }
      apply StronglySorted_inv in Hsort as (Hsort&_).
      apply StronglySorted_inv in Hsort as (Hsort&hd).
      assert (node_key succ < k); last by lia.
      apply forall_node_lt_Zlt in hd.
      eapply Forall_forall; eauto.
      by apply elem_of_list_In.
    - rewrite //=. intros Hsort ? Hin.
      inversion Hin.
      * subst.
        exfalso. apply Sorted_StronglySorted in Hsort; last first.
        { unfold Relations_1.Transitive; apply node_lt_transitive. }
        apply StronglySorted_inv in Hsort as (Hsort&Hhd).
        assert (node_lt a pred); last first.
        { unfold node_lt in *. lia. }
        eapply Forall_forall; eauto.
        apply elem_of_list_In.
        apply in_app_iff. right. by left.
      * eapply IHL1; eauto.
        apply Sorted_inv in Hsort; intuition.
  Qed.

  Lemma sorted_node_lt_hd_nin (x: node_rep) (L: list node_rep):
    Sorted node_lt (x :: L) → x ∉ L.
  Proof.
    induction L => Hsort.
    eauto with *.
    apply not_elem_of_cons; split.
    * apply Sorted_inv in Hsort as (?&Hhd).
      inversion Hhd; subst.
      unfold node_lt in H1. unfold node_key in H1.
      assert (x.1.1.1 ≠ a.1.1.1) by lia. congruence.
    * eapply IHL.
      apply Sorted_inv in Hsort as (Hsort&Hhd).
      apply Sorted_inv in Hsort as (?&Hhd').
      apply Sorted_cons; eauto.
      inversion Hhd'. subst.
      ** econstructor. 
      ** econstructor. inversion Hhd.
        by eapply node_lt_transitive.
  Qed.

  Lemma sorted_node_lt_NoDup (L: list node_rep):
    Sorted node_lt L → NoDup L.
  Proof.
    induction L as [|a L] => Hsorted.
    - econstructor.
    - specialize (sorted_node_lt_hd_nin a L Hsorted); auto.
      apply Sorted_inv in Hsorted as (Hsorted&?).
      econstructor; eauto.
  Qed.

  Lemma NoDup_pred_unique {A: Type} (L1 L2 L1' L2': list A) np pred1 pred2 :
    List.NoDup (L1 ++ pred1 :: np :: L2) →
    L1 ++ pred1 :: np :: L2 = L1' ++ pred2 :: np :: L2' →
    pred1 = pred2.
  Proof.
    revert L2 L1' L2'.
    induction L1 => //=.
    - intros L2 L1' L2' Hno_dup Heq.
      destruct L1' as [| a L1'].
      * rewrite //= in Heq; congruence. 
      * destruct L1' as [| b L1'].
        ** rewrite //= in Heq. assert (L2 = np :: L2') by congruence.
          subst. exfalso.
          rewrite ?NoDup_cons_iff in Hno_dup *.
          destruct Hno_dup as [Hpred Hno_dup].
          destruct Hno_dup as [Hnp Hno_dup].
          destruct Hno_dup as [Hnp' Hno_dup].
          apply Hnp. by left.
        ** rewrite //= in Heq. assert (L2 = L1' ++ (pred2 :: np :: L2')) by congruence.
          subst. 
          rewrite ?NoDup_cons_iff in Hno_dup *.
          destruct Hno_dup as [Hpred Hno_dup].
          destruct Hno_dup as [Hnp Hno_dup].
          exfalso. apply Hnp.
          apply in_or_app. right. econstructor; econstructor. auto.
    - intros L2 L1' L2' Hnd.
      destruct L1' as [| a' L1'].
      { rewrite //=.
        rewrite -NoDup_ListNoDup in Hnd *.
        rewrite NoDup_cons in Hnd; destruct Hnd as [Ha Hnd].
        rewrite NoDup_app in Hnd; destruct Hnd as [Hl1 Hnd]; destruct Hnd as [Hx Hnd].
        intros Heq.
        cut (np = pred1 ∨ In np L1).
        { intros [Heqpred1|Hin].
          * exfalso.  subst.
            rewrite NoDup_ListNoDup in Hnd *. inversion Hnd as [|? ? Hpred Hnd']; subst.
            eapply Hpred. by left.
          * exfalso.  eapply Hx. 
            ** apply elem_of_list_In; eauto.
            ** right. by left.
        }
        destruct L1.
        * rewrite //= in Heq. inversion Heq; subst; auto.
        * right. inversion Heq; subst. by left.
      }
      inversion 1; subst. eapply IHL1; eauto.
      inversion Hnd; eauto.
  Qed.
End LazylistLemmas.