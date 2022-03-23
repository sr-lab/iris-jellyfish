From Coq Require Import Sorting.Sorted.

From iris.heap_lang Require Import notation proofmode.
From iris.base_logic.lib Require Export invariants.

From SkipList.lazy_list Require Import code.


Local Open Scope Z.
Module LazyListSpec (Params: LAZYLIST_PARAMS).
  Import Params.
  Module Code := Lazylist Params.
  Export Code.

  Section Proofs.
    Context `{!heapGS Σ} (N : namespace).

    Definition oloc_to_val (ol: option loc) : val := 
      match ol with
      | None => NONEV
      | Some l => SOMEV #l
      end.
    

    (* 
    * The sequence of keys must be the same and
    * the lock invariant must hold in all nodes.
    *)
    Fixpoint list_equiv (L: list Z) (node: val) : iProp Σ :=
      match L with
      | nil =>    ∃ (t: loc) (m: bool) (l: val),
                  ⌜ node = SOMEV #t ⌝
                  ∗
                  t ↦ (#INT_MAX, NONEV, #m, l)
                  (* ∗
                  is_lock γ l ??? *)

      | h :: t => ∃ (np: loc) (n: option loc) (m: bool) (l: val),
                  ⌜ node = SOMEV #np ⌝
                  ∗
                  np ↦ (#h, oloc_to_val n, #m, l)
                  ∗
                  (* is_lock γ l ???
                  ∗ *)
                  ▷list_equiv t (oloc_to_val n)
      end.
    
    (* 
    * The invariant for the lazy list asserts that
    * the underlying set S is sorted and must contain
    * the same elements as S.
    *)
    Definition lazy_list_inv (S: gset Z) (v: val) : iProp Σ := 
      ∃ (L: list Z) (h: loc) (n: option loc) (m: bool) (l: val),
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted Z.lt ([INT_MIN] ++ L ++ [INT_MAX]) ⌝
      ∗
      ⌜ v = #h ⌝
      ∗
      h ↦ (#INT_MIN, oloc_to_val n, #m, l)
      (* ∗
      is_lock γ l ??? *)
      ∗
      list_equiv L (oloc_to_val n)
    .

    (* 
    * Asserts that v points to a heap cell that 
    * represents the set S as a lazy list.
    *)
    Definition is_lazy_list (S: gset Z) (v: val) : iProp Σ := 
      inv N (lazy_list_inv S v).

    Theorem new_spec :
      {{{ True }}}
        new #()
      {{{ v, RET v; 
        is_lazy_list ∅ v 
      }}}.
    Proof.
      iIntros (Φ) "_ HPost".
      wp_lam.
      wp_alloc t as "Ht"; wp_alloc h as "Hh".
      iMod (inv_alloc N ⊤ (lazy_list_inv ∅ #h) with "[Hh Ht]") as "Hinv".
      + iNext.
        iExists nil, h, (Some t), false, dummy_lock.
        iSplit. done. 
        iSplit. simpl. auto using HMIN_MAX. 
        iSplit. done.
        iFrame. iExists t, false, dummy_lock. by iFrame.
      + by iApply "HPost".
    Qed.

    Theorem contains_spec (S: gset Z) (v: val) (key: Z) 
      (Hrange: INT_MIN < key < INT_MAX) :
      {{{ is_lazy_list S v }}}
        contains v #key
      {{{ b, RET b; 
        is_lazy_list S v
        ∗
        ⌜ (b = #false ∧ ¬ key ∈ S)
        ∨
        (b = #true ∧ key ∈ S) ⌝
      }}}.
    Proof.
      iIntros (Φ) "#HPre HPost".
      wp_lam. wp_let. wp_bind (Load _).
      iInv N as (L h on m l) "(HPerm & HSort & >% & Hh & Hlist)" "Hclose"; subst; simpl.
      wp_load.
      iMod ("Hclose" with "[HPerm HSort Hh Hlist]") as "_".
      { iNext. iExists L, h, on, m, l. by iFrame. }
      iModIntro. wp_let. try repeat (wp_lam; wp_pures).
      destruct on as [n|] eqn:Hn; wp_match.
      + wp_op; case_bool_decide as Heq; wp_if.
        lia. clear Heq.
        admit.
      + iExFalso.
        admit.
    Admitted.
  End Proofs.
End LazyListSpec.