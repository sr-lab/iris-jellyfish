From Coq Require Import Lia.
From Coq Require Import Sorting.Sorted.

From iris.heap_lang Require Import notation.

From SkipList.skip_list Require Import code node_rep.


Local Open Scope Z.

Module NodeLt (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module Code := SkipList Params.
  Export Code.


  Definition node_lt (x y: node_rep) : Prop := 
    node_key x < node_key y.


  Lemma node_lt_transitive :
    forall x y z, node_lt x y → node_lt y z → node_lt x z.
  Proof.
    intros x y z. unfold node_lt.
    intros xy yz. lia.
  Qed.

  Lemma node_lt_le_incl : 
    ∀ x y, node_lt x y → node_key x ≤ node_key y.
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

  Lemma node_rep_sorted_app (L1 L2: list node_rep) :
    Sorted node_lt (L1 ++ L2) → Sorted node_lt L1 ∧ Sorted node_lt L2.
  Proof.
    induction L1.
    + rewrite //=; intros; intuition; econstructor.
    + intros Hs.
      apply Sorted_StronglySorted in Hs; last first.
      { unfold Relations_1.Transitive; apply node_lt_transitive. }
      inversion Hs; subst; eauto.
      destruct IHL1 as [HL1 HL2].
      - by apply StronglySorted_Sorted.
      - split; apply StronglySorted_Sorted.
        * apply Sorted_StronglySorted in HL1; last first.
          { unfold Relations_1.Transitive; apply node_lt_transitive. }
          constructor; first done.
          apply list.Forall_forall. intros. eapply list.Forall_forall; eauto.
          apply elem_of_list_In. apply in_or_app. left. apply elem_of_list_In; done. 
        * apply Sorted_StronglySorted.
          unfold Relations_1.Transitive; apply node_lt_transitive.
          done.
  Qed.

  Lemma forall_node_lt_Zlt (L: list node_rep) (rep: node_rep) :
    Forall (node_lt rep) L →
    Forall (Z.lt (node_key rep)) (map node_key L).
  Proof.
    induction 1; econstructor; eauto.
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

  Lemma sorted_node_lt_nin (L1 L2: list node_rep) (pred succ new: node_rep) :
    Sorted node_lt (L1 ++ [pred; succ] ++ L2) →
    node_key pred < node_key new < node_key succ →
    ¬ In new (L1 ++ [pred; succ] ++ L2).
  Proof.
    induction L1.
    - rewrite //= => Hsort Hr Hin.
      destruct Hin as [| Hin]; first (subst; lia). 
      destruct Hin as [| Hin]; first (subst; lia). 
      apply Sorted_StronglySorted in Hsort; last first.
      { unfold Relations_1.Transitive; apply node_lt_transitive. }
      apply StronglySorted_inv in Hsort as (Hsort&_).
      apply StronglySorted_inv in Hsort as (Hsort&hd).
      assert (node_key succ < node_key new); last by lia.
      apply forall_node_lt_Zlt in hd.
      eapply Forall_forall; eauto.
      by apply elem_of_list_In, in_map.
    - rewrite //=. intros Hsort Hr Hin.
      destruct Hin.
      * subst. apply Sorted_StronglySorted in Hsort; last first.
        { unfold Relations_1.Transitive; apply node_lt_transitive. }
        apply StronglySorted_inv in Hsort as (Hsort&Hhd).
        assert (node_lt new pred); last first.
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
      unfold node_lt in H1.
      assert (node_key x ≠ node_key a) by lia. congruence.
    * eapply IHL.
      apply Sorted_inv in Hsort as (Hsort&Hhd).
      apply Sorted_inv in Hsort as (?&Hhd').
      apply Sorted_cons; eauto.
      inversion Hhd'. subst.
      ** econstructor. 
      ** econstructor. inversion Hhd.
        by eapply node_lt_transitive.
  Qed.

  Lemma sorted_node_lt_no_dup (L: list node_rep):
    Sorted node_lt L → NoDup L.
  Proof.
    induction L as [|a L] => Hsorted.
    - econstructor.
    - specialize (sorted_node_lt_hd_nin a L Hsorted); auto.
      apply Sorted_inv in Hsorted as (Hsorted&?).
      econstructor; eauto.
  Qed.

  Lemma sorted_node_lt_hd (L: list node_rep) (h a: node_rep) :
    In a (h :: L) →
    Sorted node_lt (h :: L) →
    a = h ∨ node_lt h a.
  Proof.
    intros Hin Hsort.
    apply Sorted_StronglySorted in Hsort; last first.
    { unfold Relations_1.Transitive; apply node_lt_transitive. }
    apply StronglySorted_inv in Hsort as (?&Hforall).
    destruct Hin; first by left. right.
    rewrite List.Forall_forall in Hforall.
    by eapply Hforall.
  Qed.

  Lemma sorted_node_key_unique (L: list node_rep) (a b: node_rep):
    Sorted node_lt L →
    In a L →
    In b L →
    node_key a = node_key b →
    a = b.
  Proof.
    induction L as [|h L] => Hsort Hina Hinb Hkey.
    + by exfalso.
    + inversion Hina; subst.
      - clear IHL.
        apply sorted_node_lt_hd in Hinb; last auto.
        destruct Hinb as [?|Hfalse]; first auto. 
        unfold node_lt in Hfalse; lia.
      - inversion Hinb; subst.
        * clear IHL.
          apply sorted_node_lt_hd in Hina; last auto.
          destruct Hina as [?|Hfalse]; first auto. 
          unfold node_lt in Hfalse; lia.
        * apply Sorted_inv in Hsort; destruct Hsort.
          apply IHL; auto.
  Qed.
  
End NodeLt.