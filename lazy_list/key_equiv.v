From Coq Require Import Lia.
From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import gset.

From SkipList.lib Require Import misc.
From SkipList.lazy_list Require Import node_rep.


Local Open Scope Z.

Definition key_equiv (S: gset node_rep) (Skeys: gset Z) :=
  Permutation (elements Skeys) (map node_key (elements S)).

Lemma key_equiv_in (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  key_equiv S Skeys →
  rep ∈ S →
  node_key rep ∈ Skeys.
Proof.
  intros Hperm Hin.
  rewrite -elem_of_elements Hperm elem_of_list_In.
  by apply in_map, elem_of_list_In, elem_of_elements.
Qed.

Lemma key_equiv_nin (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  key_equiv S Skeys →
  ¬ node_key rep ∈ Skeys →
  ¬ rep ∈ S.
Proof.
  intros ? Hnin Hin.
  by eapply Hnin, key_equiv_in.
Qed.

Lemma key_equiv_insert_nin (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  key_equiv S Skeys →
  ¬ (node_key rep ∈ Skeys) →
  key_equiv (S ∪ {[ rep ]}) (Skeys ∪ {[ node_key rep ]}).
Proof.
  rewrite /key_equiv.
  intros ? Hnin.
  rewrite union_comm [a in Permutation _ (map _ (elements a))]@union_comm.
  rewrite ?elements_union_singleton //=.
  *** econstructor; eauto.
  *** eapply key_equiv_nin; eauto.
Qed.

Lemma key_equiv_subseteq (S1 S2: gset node_rep) (S1_keys S2_keys: gset Z) :
  key_equiv S1 S1_keys →
  key_equiv S2 S2_keys →
  S1 ⊆ S2 →
  S1_keys ⊆ S2_keys.
Proof.
  intros Hequiv1 Hequiv2 Hsub x Hin.
  rewrite /key_equiv in Hequiv1.
  rewrite -elem_of_elements elem_of_list_In Hequiv1 in Hin.
  apply in_map_iff in Hin. 
  inversion Hin as [rep (? & ?)]; subst.
  eapply key_equiv_in, Hsub; eauto.
  by rewrite -elem_of_elements elem_of_list_In.
Qed.

Lemma key_equiv_union (S S1 S2: gset node_rep) (Skeys S1_keys S2_keys: gset Z) :
  key_equiv S Skeys →
  key_equiv S1 S1_keys →
  key_equiv S2 S2_keys →
  S1 ∪ S2 ⊆ S →
  S1_keys ∪ S2_keys ⊆ Skeys →
  key_equiv (S1 ∪ S2) (S1_keys ∪ S2_keys).
Proof.
  intros Hequiv Hequiv1 Hequiv2 HinS HinSkeys.
  rewrite /key_equiv.
  apply NoDup_Permutation.
  + apply NoDup_elements.
  + apply no_dup_inj_in_map; last apply NoDup_elements.
    intros x y Hinx Hiny Hkey.

    assert (List.NoDup (elements Skeys)) as Hnd'.
    { apply NoDup_ListNoDup, NoDup_elements. }
    pose proof (Permutation_NoDup Hequiv Hnd') as Hnd.
    clear Hnd'. apply NoDup_ListNoDup in Hnd.
    
    rewrite -elem_of_list_In elem_of_elements in Hinx.
    rewrite -elem_of_list_In elem_of_elements in Hiny.
    assert (x ∈ S) as Hinx' by set_solver.
    assert (y ∈ S) as Hiny' by set_solver.
    rewrite -elem_of_elements elem_of_list_In in Hinx'.
    rewrite -elem_of_elements elem_of_list_In in Hiny'.

    induction (elements S) as [|h L]; inversion Hinx'; subst.
    - clear IHL.
      inversion Hnd as [|? ? Hnin]; subst.
      destruct Hiny'; first auto.
      rewrite Hkey elem_of_list_In in Hnin.
      destruct Hnin. by apply in_map.
    - inversion Hiny'; subst.
      * clear IHL.
        inversion Hnd as [|? ? Hnin]; subst.
        rewrite -Hkey elem_of_list_In in Hnin.
        destruct Hnin. by apply in_map.
      * inversion Hnd; subst.
        by apply IHL.
  + intros k; split.
    - intros Hin_elem%elem_of_elements.
      apply elem_of_union in Hin_elem as [Hin|Hin].
      * assert (k ∈ map node_key (elements S1)) as Hin_map.
        { rewrite -Hequiv1 elem_of_elements //. }
        rewrite elem_of_list_In in_map_iff in Hin_map.
        inversion Hin_map as [rep (? & Hin_elem)]; subst.
        rewrite elem_of_list_In in_map_iff.
        exists rep; split; first done.
        apply elem_of_list_In, elem_of_elements, elem_of_union_l.
        rewrite -elem_of_elements elem_of_list_In //.
      * assert (k ∈ map node_key (elements S2)) as Hin_map.
        { rewrite -Hequiv2 elem_of_elements //. }
        rewrite elem_of_list_In in_map_iff in Hin_map.
        inversion Hin_map as [rep (? & Hin_elem)]; subst.
        rewrite elem_of_list_In in_map_iff.
        exists rep; split; first done.
        apply elem_of_list_In, elem_of_elements, elem_of_union_r.
        rewrite -elem_of_elements elem_of_list_In //.
    - intros Hin_map%elem_of_list_In.
      rewrite in_map_iff in Hin_map.
      inversion Hin_map as [rep (? & Hin_elem)]; subst.
      apply elem_of_list_In, elem_of_elements, elem_of_union in Hin_elem as [Hin|Hin].
      * apply elem_of_elements, elem_of_union_l.
        rewrite -elem_of_elements Hequiv1 elem_of_list_In in_map_iff.
        exists rep; split; first done.
        rewrite -elem_of_list_In elem_of_elements //.
      * apply elem_of_elements, elem_of_union_r.
        rewrite -elem_of_elements Hequiv2 elem_of_list_In in_map_iff.
        exists rep; split; first done.
        rewrite -elem_of_list_In elem_of_elements //.
Qed.