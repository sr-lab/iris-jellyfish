From iris.algebra Require Import gset.

From SkipList.lib Require Import misc node_rep.


Local Open Scope Z.

Definition key_equiv (S: gset node_rep) (Skeys: gset Z) :=
  Permutation (elements Skeys) (map node_key (elements S)).

Definition set_key_equiv (S: gset node_rep) (Skeys: gset Z) :=
  Skeys = set_map node_key S.


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

Lemma set_key_equiv_in (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  set_key_equiv S Skeys →
  rep ∈ S →
  node_key rep ∈ Skeys.
Proof.
  intros Heq Hin.
  rewrite Heq elem_of_map.
  by exists rep.
Qed.

Lemma set_key_equiv_nin (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  set_key_equiv S Skeys →
  node_key rep ∉ Skeys →
  rep ∉ S.
Proof.
  intros ? Hnin Hin.
  by eapply Hnin, set_key_equiv_in.
Qed.

Lemma set_key_equiv_insert_nin (rep: node_rep) (S: gset node_rep) (Skeys: gset Z):
  set_key_equiv S Skeys →
  node_key rep ∉ Skeys →
  set_key_equiv (S ∪ {[ rep ]}) (Skeys ∪ {[ node_key rep ]}).
Proof.
  intros Heq Hnin.
  rewrite /set_key_equiv Heq set_map_union_L set_map_singleton_L //.
Qed.