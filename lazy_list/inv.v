From iris.base_logic.lib Require Export invariants.

From SkipList.lib Require Export lemmas lock.


Local Open Scope Z.
Module LazyListInv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module Lemmas := LazyListLemmas Params.
  Export Lemmas.

  Section Proofs.
    Context `{!heapGS Σ, lockG Σ} (N : namespace).

    Definition node_inv (l: loc) : iProp Σ := 
        (∃ (rep': node_rep), l ↦{#1 / 2} rep_to_node rep').
    
    (* 
    * The invariant for the lazy list asserts that
    * there exists an abstract list L equivalent to 
    * the in-memory list. The underlying list L is 
    * sorted and must contain the same elements as 
    * the abstract set S.
    *)

    Fixpoint list_equiv (L: list node_rep) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (l: loc) (γ: gname), 
                 ⌜ node_next pred = Some l ⌝
                 ∗
                 l ↦{#1 / 2} rep_to_node tail
                 ∗
                 is_lock γ (node_lock pred) (node_inv l)

        | succ :: t => ∃ (l: loc) (γ: gname), 
                       ⌜ node_next pred = Some l ⌝
                       ∗
                       l ↦{#1 / 2} rep_to_node succ
                       ∗
                       is_lock γ (node_lock pred) (node_inv l)
                       ∗
                       list_equiv succs
        end
      end.

    Definition lazy_list_inv (S: gset node_rep) (head: node_rep) : iProp Σ := 
      ∃ (L: list node_rep),
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      list_equiv ([head] ++ L)
    .

    Definition is_lazy_list (Skeys: gset Z) (v: val) : iProp Σ := 
      ∃ (head: node_rep) (S: gset node_rep),
      ⌜ key_equiv S Skeys ⌝
      ∗
      ⌜ rep_to_node head = v ⌝
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      inv N (lazy_list_inv S head).
    

    Lemma list_equiv_cons (rep: node_rep) (L: list node_rep) :
      list_equiv (rep :: L)
        ⊢ (list_equiv L ∗ (list_equiv L -∗ list_equiv (rep :: L)))
    .
    Proof.
      destruct L as [|n].
      * iIntros "Hrep". by iFrame.
      * iIntros "Hlist". iDestruct "Hlist" as (l γ) "(Hsome & Hpt & Hlock & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists l, γ. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep):
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L ⊢ ∃ (l: loc) (γ: gname),
                       ⌜ node_next pred = Some l ⌝
                       ∗
                       l ↦{#1 / 2} (rep_to_node succ)
                       ∗
                       is_lock γ (node_lock pred) (node_inv l)
                       ∗
                       (l ↦{#1 / 2} (rep_to_node succ) -∗ list_equiv L)
    .
    Proof.
      revert L. induction L1 => L HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (l γ) "(#Hsome & Hpt & #Hlock)".
          iExists l, γ. iFrame "#"; iFrame.
          iIntros "Hpt". 
          iExists l, γ. iFrame "#"; iFrame.
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (l γ) "(#Hsome & Hpt & #Hlock & Hmatch)".
          iExists l, γ. iFrame "#"; iFrame.
          iIntros "Hpt". 
          iExists l, γ. iFrame "#"; iFrame.
      + destruct L as [|curr L].
        { 
          exfalso. inversion HL  as [[H0 HL']]; subst. 
          destruct L1; inversion HL'.
        }
        inversion HL as [[H0 HL']]; subst.

        destruct L as [|curr L].
        { 
          exfalso. 
          destruct L1; inversion HL. 
          destruct L1; inversion HL.
        }
        
        iIntros "Hlist".
        iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof (IHL1 with "Hlist") as "Hlist"; auto.
        iDestruct "Hlist" as (l γ) "(Hsome & Hpt & Hlock & Himp')".
        iExists l, γ. iFrame. iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

  End Proofs.
End LazyListInv.