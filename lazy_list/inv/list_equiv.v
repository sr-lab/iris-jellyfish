From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.


Local Open Scope Z.

Module ListEquiv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module LazyList := LazyList Params.
  Export LazyList.

  Section Proofs.
    Context `{!heapGS Σ, !lockG Σ} (N : namespace).

    Definition in_lock (l: loc) : iProp Σ := 
      ∃ (succ: node_rep), l ↦{#1 / 2} rep_to_node succ.

    Fixpoint list_equiv (L: list node_rep) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (γ: gname),
                 node_next pred ↦{#1 / 2} rep_to_node tail
                 ∗
                 is_lock γ (node_lock pred) (in_lock (node_next pred))

        | succ :: t => ∃ (γ: gname),
                       node_next pred ↦{#1 / 2} rep_to_node succ
                       ∗
                       is_lock γ (node_lock pred) (in_lock (node_next pred))
                       ∗
                       list_equiv succs
        end
      end.
    

    Lemma list_equiv_cons (rep: node_rep) (L: list node_rep) :
      list_equiv (rep :: L)
        ⊢ (list_equiv L ∗ (list_equiv L -∗ list_equiv (rep :: L))).
    Proof.
      destruct L as [|n].
      + iIntros "Hrep". by iFrame.
      + iIntros "Hlist". iDestruct "Hlist" as (γ) "(Hpt & Hlock & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists γ. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep) :
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L ⊢ 
        node_next pred ↦{#1 / 2} rep_to_node succ
        ∗
        (node_next pred ↦{#1 / 2} rep_to_node succ -∗ list_equiv L).
    Proof.
      revert L. induction L1 => L HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ) "(Hpt & #Hlock)".
          iFrame. iIntros "Hpt". 
          iExists γ. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ) "(Hpt & #Hlock & Hmatch)".
          iFrame. iIntros "Hpt". 
          iExists γ. iFrame "# ∗".
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
        iDestruct "Hlist" as "(Hpt & Himp')".
        iFrame. iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert (L: list node_rep) (head pred: node_rep) :
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) ⊢ 
        ∃ (succ: node_rep) (γ: gname), 
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          node_next pred ↦{#1/2} rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          (node_next pred ↦{#1/2} rep_to_node succ -∗ list_equiv ([head] ++ L)).
    Proof.
      intros Hin; inversion Hin as [|Hin_L]; subst.
      + iIntros "Hlist". destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ) "(Hpt & #Hlock)".
          iExists tail, γ. iFrame; iFrame "#".
          iSplit; first by iRight.
          iIntros "Hpt". iExists γ.
          by iFrame; iFrame "#".
        - iDestruct "Hlist" as (γ) "(Hpt & #Hlock & ?)".
          iExists succ', γ. iFrame; iFrame "#".
          iSplit; first by repeat iLeft.
          iIntros "Hpt". iExists γ.
          by iFrame; iFrame "#".
      + simpl in Hin_L; clear Hin.
        iIntros "Hlist".
        iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iRevert (head Hin_L) "Hlist Himp".
        iInduction L as [|succ' L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
        iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist Himp".
        - destruct L as [|succ'' L]; subst.
          * iDestruct "Hlist" as (γ) "(Hpt & #Hlock)".
            iExists tail, γ. iFrame; iFrame "#".
            iSplit; first by iRight.
            iIntros "Hpt". iApply "Himp". iExists γ. 
            by iFrame; iFrame "#".
          * iDestruct "Hlist" as (γ) "(Hpt & #Hlock & Hmatch)".
            iExists succ'', γ. 
            iSplit; first by iLeft; iRight; iLeft.
            iFrame "Hpt"; iFrame "Hlock".
            iIntros "Hpt". iApply "Himp".
            iExists γ. by iFrame; iFrame "#".
        - iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp')".
          iPoseProof ("IHL" with "Hin") as "Himp''".
          iPoseProof ("Himp''" with "Hlist") as "Himp''".
          iPoseProof ("Himp''" with "Himp'") as "Hlist".
          iDestruct "Hlist" as (succ γ) "(Hsucc & Hpt & Hlock & Himp')".
          iExists succ, γ. iFrame; iFrame "#".
          iSplit.
          {
            iDestruct "Hsucc" as "[Hin|Heq]".
            by iLeft; iRight. by iRight.
          }
          iIntros "Hpt".
          iApply "Himp". by iApply "Himp'".
    Qed.

    Lemma list_equiv_insert (head pred new succ: node_rep) (L: list node_rep) 
      (γ': gname) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) ⊢ 
        node_next pred ↦{#1/2} rep_to_node succ 
        ∗ 
        node_next new ↦{#1/2} rep_to_node succ
        ∗
        is_lock γ' (node_lock new) (in_lock (node_next new))
        -∗ 
          ∃ (L' L1 L2: list node_rep), 
            node_next pred ↦ rep_to_node succ
            ∗
            ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
            ∗
            ⌜ Sorted node_lt ([head] ++ L' ++ [tail]) ⌝
            ∗
            ⌜ Permutation ([head] ++ L') ([head; new] ++ L) ⌝ 
            ∗
            (node_next pred ↦{#1/2} (rep_to_node new) -∗ list_equiv ([head] ++ L')).
    Proof.
      iIntros (Hnew Hrange Hsort Hin) "Hlist (Hpt & Hpt' & Hlock')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L HeqL' Hsort Hin) "Hlist Hpt Hpt' Hlock'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L Hfalse); inversion Hfalse. }

      iIntros (head L HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist Hpt Hpt' #Hlock'".
        destruct L as [|a L].
        - iDestruct "Hlist" as (γ) "(Hpt'' & #Hlock)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Htail%rep_to_node_inj; subst.
          iExists (new :: nil), nil, nil.
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor; auto.
            unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ. iFrame "# ∗".
          iExists γ'. iFrame "#".
        - iDestruct "Hlist" as (γ) "(Hpt'' & #Hlock & Hmatch)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq%rep_to_node_inj; subst.
          iExists (new :: a :: L), nil, (L ++ [tail]).
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro.
            repeat apply Sorted_inv in Hsort as (Hsort&?).
            repeat econstructor; auto. 
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ. iFrame "# ∗".
          iExists γ'. iFrame "#".
      + destruct L as [|head' L]; first by inversion HinL.
        iIntros "Hlist Hpt Hpt' #Hlock'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (γ) "(Hpt'' & Hlock & Hmatch)".
        iPoseProof ("IHL'" $! head' L with "[%] [%] [%] [$] [$] [$] [$]") 
          as "Hclose"; auto.
        
        iDestruct "Hclose" as (L' L1 L2) "(Hpt' & %Hsplit & %Hsort' & %Hperm' & Himp')".
        iExists (head' :: L'), (head :: L1), L2. iFrame.
        iSplit.
        {
          rewrite /= in Hsplit.
          rewrite /= Hsplit //.
        }
        iSplit.
        {
          iPureIntro. inversion Hhd.
          apply Sorted_inv in Hsort' as (Hsort'&?).
          repeat econstructor; auto.
        }
        iSplit.
        {
          iPureIntro. 
          simpl in Hperm'; rewrite Hperm'. 
          econstructor; econstructor.
        }

        iIntros "Hpt". iExists γ.
        iPoseProof ("Himp'" with "Hpt") as "Hlist".
        iFrame.
    Qed.

  End Proofs.
End ListEquiv.