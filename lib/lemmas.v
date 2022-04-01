From Coq Require Import Lia Sorting.Sorted.

From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.


Local Open Scope Z.

Lemma node_lt_transitive :
  forall x y z, node_lt x y -> node_lt y z -> node_lt x z
.
Proof.
  intros x y z. unfold node_lt.
  intros xy yz. lia.
Qed.

Lemma node_rep_sorted_eq (l l': list node_rep):
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

Lemma StronglySorted_app {A: Type} R (L1 L2: list A):
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

Lemma node_rep_sorted_app (L1 L2: list node_rep):
  Sorted node_lt (L1 ++ L2) → Sorted node_lt L1 ∧ Sorted node_lt L2.
Proof.
  intros HS. apply Sorted_StronglySorted in HS; last eauto with *.
  + apply StronglySorted_app in HS as (?&?); split; eauto using StronglySorted_Sorted.
  + unfold Relations_1.Transitive.
    apply node_lt_transitive.
Qed.