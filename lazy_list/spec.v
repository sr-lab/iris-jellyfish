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
        ⊢ list_equiv L ∗ (list_equiv L -∗ list_equiv (rep :: L))
    .
    Proof.
      destruct L as [|n].
      * iIntros "Hrep". iDestruct "Hrep" as (l) "(? & ? & ?)".
        iSplit. done. iIntros. 
        iExists l. iFrame.
      * iIntros "Hrep". iDestruct "Hrep" as (l) "(? & ? & ?)".
        iFrame. iIntros. 
        iExists l. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep):
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L ⊢ ∃ (l: loc),
                     ⌜ node_next pred = Some l ⌝
                     ∗
                     l ↦ (rep_to_node succ)
                     ∗
                     (⌜ node_next pred = Some l ⌝ ∗ l ↦ (rep_to_node succ) -∗ list_equiv L)
    .
    Proof.
      revert L. induction L1 => L Heq.
      + destruct L as [|curr L].
        { exfalso. inversion Heq. }
        inversion Heq as [[H0 Heq']]; subst.
        destruct L as [| curr L].
        - inversion Heq'; subst.
          iIntros "Hpred". iDestruct "Hpred" as (t) "(Hsome & Hpt)".
          iExists t. iFrame.
          iIntros "Htail". iExists t. iFrame.
        - inversion Heq'; subst.
          iIntros "Hpred". iDestruct "Hpred" as (n) "(Hsome & Hpt & Hmatch)".
          iExists n. iFrame.
          iIntros "succ".
          iExists n. iFrame.
      + destruct L as [| curr L].
        { 
          exfalso. inversion Heq  as [[H0 Heq']]; subst. 
          destruct L1; inversion Heq'.
        }
        inversion Heq  as [[H0 Heq']]; subst.
        iIntros "Hlist".
        iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof (IHL1 with "Hlist") as "Hpred". { done. }
        iDestruct "Hpred" as (l) "(Hsome & Hpt & Hmatch)".
        iExists l. iFrame. iIntros "(Hsome & Hpt)".
        iApply "Himp". iApply "Hmatch". iFrame. 
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
      iIntros (Φ) "(#Hinv&Hcurr_range&Hcurr_key) HΦ".
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

        destruct Lm as [|ck' Lm].
        - rewrite (list_equiv_split curr succ ([head] ++ L)); last first.
          { simpl in *. by rewrite -Hsplit_sep. }

          admit.
        - admit.
      + admit.
    Admitted.

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