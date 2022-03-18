From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.

Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

  Context `{!heapGS Σ} (N : namespace).

  (* 
  * The sequence of keys must be the same and
  * the lock invariant must hold in all nodes.
  *)
  Fixpoint list_equiv (L: list Z) (node: val) : iProp Σ :=
    match L with
    | nil => ⌜ node = NONEV ⌝
    | h :: t => ∃ (k: Z) (n: loc) (m: bool) (l: val) (v': val) (γ: gname),
                ⌜ node = rep_to_node (k, n, m, l) ⌝
                ∗
                ⌜ k = h ⌝
                ∗
                n ↦ v'
                ∗
                (* is_lock γ l ???
                ∗ *)
                ▷list_equiv t v'
    end.

  (* 
  * The invariant for the lazy list asserts that
  * the underlying set S is sorted and must contain
  * the same elements as S.
  *)
  Definition lazy_list_inv (S: gset Z) (l: loc) : iProp Σ := 
    ∃ (L: list Z) (head: val),
    ⌜ Permutation L (elements S) ⌝
    ∗
    (* ⌜ Sorted Zlt L ⌝
    ∗ *)
    l ↦ head
    ∗
    list_equiv ([INT_MIN] ++ L ++ [INT_MAX]) head
  .

  (* 
  * Asserts that l points to a heap cell that 
  * represents the set S as a lazy list.
  *)
  Definition is_lazy_list (S: gset Z) (v: val) : iProp Σ := 
    ∃ (l: loc), ⌜v = #l⌝ ∗ inv N (lazy_list_inv S l).

  Theorem new_spec (S: gset Z) :
    {{{ True }}}
      new #()
    {{{ (v: val), RET v; 
      is_lazy_list ∅ v 
    }}}.
  Proof.
  Admitted.

  (* Theorem contains_spec (S: gset Z) (v: val) (key: Z) :
    {{{ is_lazy_list S v }}}
      contains !v #key
    {{{ (b: bool), RET b; 
      is_lazy_list S v
      ∗
      ⌜ (b = false ∧ ¬ key ∈ S)
      ∨
      (b = true ∧ key ∈ S) ⌝
    }}}.
  Proof.
  Admitted. *)

End LazyListSpec.