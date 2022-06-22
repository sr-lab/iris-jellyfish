From Coq Require Import Lia.
From Coq Require Import Sorting.Sorted.

From iris.algebra Require Import gset.

From SkipList.lib Require Import misc.
From SkipList.lazy_list Require Import node_lt code node_rep.


Local Open Scope Z.

Module KeyEquiv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module NodeLt := NodeLt Params.
  Export NodeLt.


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
    node_key rep ∉ Skeys →
    rep ∉ S.
  Proof.
    intros ? Hnin Hin.
    by eapply Hnin, key_equiv_in.
  Qed.

  Lemma key_equiv_insert_nin (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
    key_equiv S Skeys →
    node_key rep ∉ Skeys →
    key_equiv (S ∪ {[ rep ]}) (Skeys ∪ {[ node_key rep ]}).
  Proof.
    rewrite /key_equiv.
    intros ? Hnin.
    rewrite union_comm [a in Permutation _ (map _ (elements a))]@union_comm.
    rewrite ?elements_union_singleton //=.
    + econstructor; eauto.
    + eapply key_equiv_nin; eauto.
  Qed.

End KeyEquiv.