From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.

From Coq Require Import Lists.ListSet.

Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

Context `{!heapGS Σ} (N : namespace).

Fixpoint list_equiv (L: list Z) (node: val) : iProp Σ :=
  match L with
  | nil => ⌜ node = NONEV ⌝
  | h :: t => ∃ (k: Z) (n: loc) (m: bool) (l: val) (v': val) (γ: gname),
              ⌜ node = rep_to_node (k, n, m, l) ⌝
              ∗
              n ↦ v'
              ∗
              (* is_lock γ l ???
              ∗ *)
              list_equiv t v'
  end.

Definition lazy_list_inv (S: set Z) (l: loc) : iProp Σ := 
  ∃ (L: list Z) (head: val),
  (* ⌜ Permutation L (elements S) ⌝
  ∗ *)
  (* ⌜ Sorted Zlt L ⌝
  ∗ *)
  l ↦ head
  ∗
  list_equiv L head
.

Definition is_lazy_list (S: set Z) (l: loc) : iProp Σ := 
  inv N (lazy_list_inv S l).

Definition empty_lazy := [INT_MIN; INT_MAX].

Theorem new_spec :
  {{{ True }}}
    new #()
  {{{ l, RET l; 
    is_lazy_list empty_lazy l 
  }}}.
Proof.
Admitted.

Theorem contains_spec (S: set Z) (l: loc) (key: Z) :
  {{{ is_lazy_list S l }}}
    contains !#l #key
  {{{ b, RET b; 
    is_lazy_list S l
    ∗
    ⌜ (b = False ∧ ¬ key ∈ S)
    ∨
    (b = True ∧ key ∈ S) ⌝
  }}}.
Proof.
Admitted.