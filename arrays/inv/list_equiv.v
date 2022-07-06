From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.arrays Require Import code.


Local Open Scope Z.

Module ListEquiv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module SkipList := SkipList Params.
  Export SkipList.

  Section Proofs.
    Context `{!heapGS Σ, !lockG Σ} (lvl: Z).

    Definition nodeN (rep: node_rep) := nroot .@ "node" .@ rep.

    Definition node_inv(s: loc) (succ: node_rep) : iProp Σ := 
      s ↦{#1 / 2} rep_to_node succ.

    Definition in_lock (next: loc) : iProp Σ := 
      ∃ (vs: list val), next ↦∗{#1 / 2} vs.

    Fixpoint list_equiv (L: list node_rep) (P: node_rep → iProp Σ) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (γ: gname) (t: loc), 
                 (node_next pred +ₗ lvl) ↦{#1 / 2} #t
                 ∗
                 inv (nodeN tail) (node_inv t tail)
                 ∗
                 is_lock γ (node_lock pred) (in_lock (node_next pred))

        | succ :: _ => ∃ (γ: gname) (s: loc), 
                       (node_next pred +ₗ lvl) ↦{#1 / 2} #s
                       ∗
                       inv (nodeN succ) (node_inv s succ)
                       ∗
                       is_lock γ (node_lock pred) (in_lock (node_next pred))
                       ∗
                       P succ
                       ∗
                       list_equiv succs P
        end
      end. 
    

    Lemma list_equiv_cons (rep: node_rep) (L: list node_rep)
      (P: node_rep → iProp Σ) :
      list_equiv (rep :: L) P ⊢ 
        (list_equiv L P ∗ (list_equiv L P -∗ list_equiv (rep :: L) P)).
    Proof.
      destruct L as [|n].
      + iIntros "Hrep". by iFrame.
      + iIntros "Hlist". iDestruct "Hlist" as (γ s) "(Hpt & Hs & Hlock & HP & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists γ, s. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep) 
      (P: node_rep → iProp Σ) :
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L P ⊢ 
        ∃ (γ: gname) (s: loc),
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          inv (nodeN succ) (node_inv s succ)
          ∗
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          ((node_next pred +ₗ lvl) ↦{#1 / 2} #s -∗ list_equiv L P).
    Proof.
      revert L. induction L1 => L HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist".
          iDestruct "Hlist" as (γ t) "(Hpt & #Ht & #Hlock)".
          iExists γ, t. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, t. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ s) "(Hpt & #Hs & #Hlock & Hmatch)".
          iExists γ, s. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, s. iFrame "# ∗".
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
        iDestruct "Hlist" as (γ s) "(Hpt & #Hs & Hlock & Himp')".
        iExists γ, s. iFrame "# ∗". 
        iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert_L (L: list node_rep) (head pred: node_rep) 
      (P: node_rep → iProp Σ) :
      In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        ∃ (s: loc) (succ: node_rep) (L1 L2: list node_rep) (γ: gname), 
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          inv (nodeN succ) (node_inv s succ)
          ∗ 
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          P pred
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s ∗ P pred -∗ list_equiv ([head] ++ L) P).
    Proof.
      iIntros (Hin) "Hlist".
      iRevert (head Hin) "Hlist".
      iInduction L as [|succ L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
      iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist".
      + iDestruct "Hlist" as (γ s) "(Hpt & #Hs & #Hlock & HP & Hlist)".
        destruct L as [|succ' L]; subst.
        - iDestruct "Hlist" as (γ' t) "(Hpt' & #Ht & #Hlock')".
          iExists t, tail, [head], nil, γ'. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "(Hpt' & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ' s') "(Hpt' & #Hs' & #Hlock' & Hmatch)".
          iExists s', succ', [head], (L ++ [tail]), γ'. iFrame "# ∗".
          iSplit; first by iLeft; iRight; iLeft. iSplit; first done.
          iIntros "(Hpt' & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', s'. iFrame "# ∗".
      + iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof ("IHL" with "Hin") as "Himp'".
        iPoseProof ("Himp'" with "Hlist") as "Hlist".
        iDestruct "Hlist" as (s' succ' L1 L2 γ) "(%Hsucc' & %Hsplit & Hpt & #Hs' & Hlock & HP & Himp')".
        iExists s', succ', ([head] ++ L1), L2, γ. iFrame "# ∗".
        iSplit.
        { iPureIntro. destruct Hsucc'; first left; by right. }
        iSplit.
        { iPureIntro; simpl in *; by rewrite Hsplit. }
        iIntros "(Hpt' & HP)". 
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert (L: list node_rep) (head pred: node_rep) 
      (P: node_rep → iProp Σ) :
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        ∃ (s: loc) (succ: node_rep) (L1 L2: list node_rep) (γ: gname),
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          inv (nodeN succ) (node_inv s succ)
          ∗ 
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s -∗ list_equiv ([head] ++ L) P).
    Proof.
      intros Hin; destruct Hin as [Heq|Hin]; first subst.
      + iIntros "Hlist". destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ t) "(Hpt & #Ht & #Hlock)".
          iExists t, tail, nil, nil, γ. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "Hpt". 
          iExists γ, t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ s') "(Hpt & #Hs' & #Hlock & ?)".
          iExists s', succ', nil, (L ++ [tail]), γ. iFrame "# ∗".
          iSplit; first by repeat iLeft. iSplit; first done.
          iIntros "Hpt". 
          iExists γ, s'. iFrame "# ∗".
      + iIntros "Hlist".
        iPoseProof (list_equiv_invert_L with "Hlist") as "Hlist"; first done.
        iDestruct "Hlist" as (s succ L1 L2 γ) "(? & ? & ? & ? & ? & ? & Himp)".
        iExists s, succ, L1, L2, γ. iFrame.
        iIntros "?". iApply "Himp". iFrame.
    Qed.

  End Proofs.
End ListEquiv.