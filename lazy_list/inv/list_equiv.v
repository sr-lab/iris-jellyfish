From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import node_lt node_rep code key_equiv.


Local Open Scope Z.
Module ListEquiv (Params: LAZY_LIST_PARAMS).
  Import Params.
  Module KeyEquiv := KeyEquiv Params.
  Export KeyEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !lockG Σ} (N : namespace).

    Definition node_inv (l: loc) : iProp Σ := 
      ∃ (succ: node_rep), l ↦{#1 / 2} rep_to_node succ.

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
    

    Lemma list_equiv_cons (rep: node_rep) (L: list node_rep) :
      list_equiv (rep :: L)
        ⊢ (list_equiv L ∗ (list_equiv L -∗ list_equiv (rep :: L))).
    Proof.
      destruct L as [|n].
      + iIntros "Hrep". by iFrame.
      + iIntros "Hlist". iDestruct "Hlist" as (l γ) "(Hsome & Hpt & Hlock & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists l, γ. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep) :
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L ⊢ 
        ∃ (l: loc) (γ: gname),
          ⌜ node_next pred = Some l ⌝
          ∗
          l ↦{#1 / 2} (rep_to_node succ)
          ∗
          is_lock γ (node_lock pred) (node_inv l)
          ∗
          (l ↦{#1 / 2} (rep_to_node succ) -∗ list_equiv L).
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

    Lemma list_equiv_invert (L: list node_rep) (head pred: node_rep) :
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) ⊢ 
        ∃ (succ: node_rep) (l: loc) (γ: gname), 
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          ⌜ node_next pred = Some l ⌝
          ∗
          l ↦{#1/2} (rep_to_node succ)
          ∗ 
          is_lock γ (node_lock pred) (node_inv l)
          ∗
          (l ↦{#1/2} (rep_to_node succ) -∗ list_equiv ([head] ++ L)).
    Proof.
      intros Hin; inversion Hin as [|Hin_L]; subst.
      + iIntros "Hlist". destruct L as [|succ' L].
        - iDestruct "Hlist" as (l γ) "(%Hsome & Hpt & #Hlock)".
          iExists tail, l, γ. iFrame; iFrame "#".
          iSplit; first by iRight. iSplit; first done.
          iIntros "Hpt". iExists l, γ.
          by iFrame; iFrame "#".
        - iDestruct "Hlist" as (l γ) "(%Hsome & Hpt & #Hlock & ?)".
          iExists succ', l, γ. iFrame; iFrame "#".
          iSplit; first by repeat iLeft. iSplit; first done. 
          iIntros "Hpt". iExists l, γ.
          by iFrame; iFrame "#".
      + simpl in Hin_L; clear Hin.
        iIntros "Hlist".
        iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iRevert (head Hin_L) "Hlist Himp".
        iInduction L as [|succ' L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
        iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist Himp".
        - destruct L as [|succ'' L]; subst.
          * iDestruct "Hlist" as (l γ) "(%Hsome & Hpt & #Hlock)".
            iExists tail, l, γ. iFrame; iFrame "#".
            iSplit; first by iRight. iSplit; first done.
            iIntros "Hpt". iApply "Himp". iExists l, γ. 
            by iFrame; iFrame "#".
          * iDestruct "Hlist" as (l γ) "(%Hsome & Hpt & #Hlock & Hmatch)".
            iExists succ'', l, γ. 
            iSplit; first by iLeft; iRight; iLeft. iSplit; first done.
            iFrame "Hpt"; iFrame "Hlock".
            iIntros "Hpt". iApply "Himp".
            iExists l, γ. by iFrame; iFrame "#".
        - iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp')".
          iPoseProof ("IHL" with "Hin") as "Himp''".
          iPoseProof ("Himp''" with "Hlist") as "Himp''".
          iPoseProof ("Himp''" with "Himp'") as "Hlist".
          iDestruct "Hlist" as (succ l γ) "(Hsucc & Hsome & Hpt & Hlock & Himp')".
          iExists succ, l, γ. iFrame; iFrame "#".
          iSplit.
          {
            iDestruct "Hsucc" as "[Hin|Heq]".
            by iLeft; iRight. by iRight.
          }
          iIntros "Hpt".
          iApply "Himp". by iApply "Himp'".
    Qed.

    Lemma list_equiv_insert (head pred new succ: node_rep) (L: list node_rep) 
      (l l': loc) (γ': gname) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) ⊢ 
        ⌜ node_next pred = Some l ⌝ ∗ l↦{#1/2} rep_to_node succ 
        ∗ 
        ⌜ node_next new = Some l' ⌝ ∗ l'↦{#1/2} rep_to_node succ
        ∗
        is_lock γ' (node_lock new) (node_inv l')
        -∗ 
          ∃ (L' L1 L2: list node_rep), 
            l ↦ rep_to_node succ
            ∗
            ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
            ∗
            ⌜ Sorted node_lt ([head] ++ L' ++ [tail]) ⌝
            ∗
            ⌜ Permutation ([head] ++ L') ([head; new] ++ L) ⌝ 
            ∗
            (l ↦{#1/2} (rep_to_node new) -∗ list_equiv ([head] ++ L')).
    Proof.
      iIntros (Hnew Hrange Hsort Hin) "Hlist (Hsome & Hpt & Hsome' & Hpt' & Hlock')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L HeqL' Hsort Hin) "Hlist Hsome Hpt Hsome' Hpt' Hlock'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L Hfalse); inversion Hfalse. }

      iIntros (head L HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist %Hsome Hpt %Hsome' Hpt' #Hlock'".
        destruct L as [|a L].
        - iDestruct "Hlist" as (l'' γ) "(%Hsome'' & Hpt'' & #Hlock)".
          assert (l = l'') as <- by congruence.
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Htail.
          apply rep_to_node_inj in Htail; subst.
          iExists (new :: nil), nil, nil.
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor; auto.
            unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". iExists _, _.
          iFrame "# ∗". iSplit; first done.
          iExists _, _. by iFrame "# ∗".
        - iDestruct "Hlist" as (l'' γ) "(%Hsome'' & Hpt'' & #Hlock & Hmatch)".
          assert (l = l'') as <- by congruence.
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          apply rep_to_node_inj in Heq; subst.
          iExists (new :: a :: L), nil, (L ++ [tail]).
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro.
            repeat apply Sorted_inv in Hsort as (Hsort&?).
            repeat econstructor; auto. 
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". iExists _, _.
          iFrame "# ∗". iSplit; first done.
          iExists _, _. by iFrame "# ∗".
      + destruct L as [|head' L]; first by inversion HinL.
        iIntros "Hlist %Hsome Hpt %Hsome' Hpt' #Hlock'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (l'' γ) "(Hsome'' & Hpt'' & Hlock & Hmatch)".
        iPoseProof ("IHL'" $! head' L with "[%] [%] [%] [$] [%] [$] [%] [$] [$]") 
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

        iIntros "Hpt". iExists l'', γ.
        iPoseProof ("Himp'" with "Hpt") as "Hlist".
        iFrame.
    Qed.

  End Proofs.
End ListEquiv.