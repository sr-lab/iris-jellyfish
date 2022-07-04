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
    Context `{!heapGS Σ, !lockG Σ} (lvl: Z) (q: frac).

    Definition node_inv (next: loc) : iProp Σ := 
      ∃ (s: loc), (next +ₗ lvl) ↦{#1 / 2} #s.

    Fixpoint list_equiv (L: list node_rep) (P: node_rep → iProp Σ) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (γ: gname) (t: loc), 
                 (node_next pred +ₗ lvl) ↦{#1 / 2} #t
                 ∗
                 t ↦{#q} rep_to_node tail
                 ∗
                 is_lock γ (node_lock pred) (node_inv (node_next pred))

        | succ :: _ => ∃ (γ: gname) (s: loc), 
                       (node_next pred +ₗ lvl) ↦{#1 / 2} #s
                       ∗
                       s ↦{#q} rep_to_node succ
                       ∗
                       is_lock γ (node_lock pred) (node_inv (node_next pred))
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
          s ↦{#q} rep_to_node succ
          ∗
          is_lock γ (node_lock pred) (node_inv (node_next pred))
          ∗
          ((node_next pred +ₗ lvl) ↦{#1 / 2} #s ∗ s ↦{#q} rep_to_node succ -∗ list_equiv L P).
    Proof.
      revert L. induction L1 => L HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist".
          iDestruct "Hlist" as (γ t) "(Hpt & Ht & #Hlock)".
          iExists γ, t. iFrame "# ∗".
          iIntros "(Hpt & Ht)". 
          iExists γ, t. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ s) "(Hpt & Hs & #Hlock & Hmatch)".
          iExists γ, s. iFrame "# ∗".
          iIntros "(Hpt & Hs)". 
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
        iDestruct "Hlist" as (γ s) "(Hpt & Hs & Hlock & Himp')".
        iExists γ, s. iFrame. iIntros "(Hpt & Hs)".
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
          s ↦{#q} rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (node_inv (node_next pred))
          ∗
          P pred
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s
           ∗
           s ↦{#q} rep_to_node succ
           ∗ 
           P pred -∗ 
           list_equiv ([head] ++ L) P).
    Proof.
      iIntros (Hin) "Hlist".
      iRevert (head Hin) "Hlist".
      iInduction L as [|succ L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
      iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist".
      + iDestruct "Hlist" as (γ s) "(Hpt & Hs & #Hlock & HP & Hlist)".
        destruct L as [|succ' L]; subst.
        - iDestruct "Hlist" as (γ' t) "(Hpt' & Ht & #Hlock')".
          iExists t, tail, [head], nil, γ'. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "(Hpt' & Ht & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ' s') "(Hpt' & Hs' & #Hlock' & Hmatch)".
          iExists s', succ', [head], (L ++ [tail]), γ'. iFrame "# ∗".
          iSplit; first by iLeft; iRight; iLeft. iSplit; first done.
          iIntros "(Hpt' & Hs' & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', s'. iFrame "# ∗".
      + iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof ("IHL" with "Hin") as "Himp'".
        iPoseProof ("Himp'" with "Hlist") as "Hlist".
        iDestruct "Hlist" as (s' succ' L1 L2 γ) "(%Hsucc' & %Hsplit & Hpt & Hs' & Hlock & HP & Himp')".
        iExists s', succ', ([head] ++ L1), L2, γ. iFrame "# ∗".
        iSplit.
        { iPureIntro. destruct Hsucc'; first left; by right. }
        iSplit.
        { iPureIntro; simpl in *; by rewrite Hsplit. }
        iIntros "(Hpt' & Hs' & HP)". 
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
          s ↦{#q} rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (node_inv (node_next pred))
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s ∗ s ↦{#q} rep_to_node succ -∗ list_equiv ([head] ++ L) P).
    Proof.
      intros Hin; destruct Hin as [Heq|Hin]; first subst.
      + iIntros "Hlist". destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ t) "(Hpt & Ht & #Hlock)".
          iExists t, tail, nil, nil, γ. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "(Hpt & Ht)". 
          iExists γ, t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ s') "(Hpt & Hs' & #Hlock & ?)".
          iExists s', succ', nil, (L ++ [tail]), γ. iFrame "# ∗".
          iSplit; first by repeat iLeft. iSplit; first done.
          iIntros "(Hpt & Hs')". 
          iExists γ, s'. iFrame "# ∗".
      + iIntros "Hlist".
        iPoseProof (list_equiv_invert_L with "Hlist") as "Hlist"; first done.
        iDestruct "Hlist" as (s succ L1 L2 γ) "(? & ? & ? & ? & ? & ? & Himp)".
        iExists s, succ, L1, L2, γ. iFrame.
        iIntros "(? & ?)". iApply "Himp". iFrame.
    Qed.

    Lemma list_equiv_insert (n s: loc) (head pred new succ: node_rep) (L: list node_rep) 
      (γ': gname) (P: node_rep → iProp Σ) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        (node_next pred +ₗ lvl) ↦{#1/2} #s
        ∗ 
        (node_next new +ₗ lvl) ↦{#1/2} #s
        ∗ 
        s ↦{#q} rep_to_node succ 
        ∗
        n ↦{#q} rep_to_node new 
        ∗
        is_lock γ' (node_lock new) (node_inv (node_next new))
        ∗
        P new
        -∗ 
          ∃ (L' L1 L2: list node_rep), 
            (node_next pred +ₗ lvl) ↦ #s
            ∗
            ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
            ∗
            ⌜ Sorted node_lt ([head] ++ L' ++ [tail]) ⌝
            ∗
            ⌜ Permutation ([head] ++ L') ([head; new] ++ L) ⌝ 
            ∗
            ((node_next pred +ₗ lvl) ↦{#1/2} #n -∗ list_equiv ([head] ++ L') P).
    Proof.
      iIntros (Hnew Hrange Hsort Hin) "Hlist (Hpt & Hpt' & Hs & Hn & Hlock' & HP')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L HeqL' Hsort Hin) "Hlist Hpt Hpt' Hs Hn Hlock' HP'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L Hfalse); inversion Hfalse. }

      iIntros (head L HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist Hpt Hpt' Hs Hn #Hlock' HP'".
        destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ t) "(Hpt'' & Ht & #Hlock)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Ht.
          assert (s = t) as -> by congruence.
          iDestruct (mapsto_agree with "Ht Hs") as %Htail%rep_to_node_inj; subst.
          iCombine "Hpt Hpt''" as "Hpt".
          iExists (new :: nil), nil, nil.
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor; auto.
            unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ, n. iFrame "# ∗".
          iExists γ', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ s') "(Hpt'' & Hs' & #Hlock & Hmatch)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Hs.
          assert (s = s') as <- by congruence.
          iDestruct (mapsto_agree with "Hs Hs'") as %Heq%rep_to_node_inj; subst.
          iExists (new :: succ' :: L), nil, (L ++ [tail]).
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro.
            repeat apply Sorted_inv in Hsort as (Hsort&?).
            repeat econstructor; auto. 
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ, n. iFrame "# ∗".
          iExists γ', s. iFrame "# ∗".
      + destruct L as [|head' L]; first by inversion HinL.
        iIntros "Hlist Hpt Hpt' Hs Hn #Hlock' HP'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (γ h') "(Hpt'' & Hh' & Hlock & HP & Hmatch)".
        iPoseProof ("IHL'" $! head' L with "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$]") 
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

        iIntros "Hpt". iExists γ, h'.
        iPoseProof ("Himp'" with "Hpt") as "Hlist".
        iFrame.
    Qed.

  End Proofs.
End ListEquiv.