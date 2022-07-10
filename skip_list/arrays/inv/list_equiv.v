From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.


Local Open Scope Z.

Module ListEquiv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module SkipList := SkipList Params.
  Export SkipList.

  Section Proofs.
    Context `{!heapGS Σ, !lockG Σ} (lvl: Z).

    Definition is_array (next: loc) (h: Z) : iProp Σ := 
      ∃ (vs: list val), next ↦∗{#1 / 2} vs ∗ ⌜ length vs = Z.to_nat h ⌝.

    Fixpoint list_equiv (L: list node_rep) (P: node_rep → iProp Σ) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (γ: gname) (h: Z) (t: loc), 
                 (node_next pred +ₗ lvl) ↦{#1 / 2} #t
                 ∗
                 t ↦□ rep_to_node tail
                 ∗
                 is_lock γ (node_lock pred) (is_array (node_next pred) h)
                 ∗
                 ⌜ lvl < h ⌝

        | succ :: _ => ∃ (γ: gname) (h: Z) (s: loc), 
                       (node_next pred +ₗ lvl) ↦{#1 / 2} #s
                       ∗
                       s ↦□ rep_to_node succ
                       ∗
                       is_lock γ (node_lock pred) (is_array (node_next pred) h)
                       ∗
                       ⌜ lvl < h ⌝
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
      + iIntros "Hlist". 
        iDestruct "Hlist" as (γ h s) "(Hpt & Hs & Hlock & Hh & HP & Hmatch)".
        iFrame. iIntros "Hlist". iFrame.
        iExists γ, h, s. iFrame.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep) 
      (P: node_rep → iProp Σ) :
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L P ⊢ 
        ∃ (s: loc),
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          s ↦□ rep_to_node succ
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
          iDestruct "Hlist" as (γ h t) "(Hpt & #Ht & #Hlock & Hh)".
          iExists t. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, h, t. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ h s) "(Hpt & #Hs & #Hlock & Hh & Hmatch)".
          iExists s. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, h, s. iFrame "# ∗".
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
        iDestruct "Hlist" as (s) "(Hpt & #Hs & Himp')".
        iExists s. iFrame "# ∗". 
        iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert_L (L: list node_rep) (head pred: node_rep) 
      (P: node_rep → iProp Σ) :
      In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        ∃ (γ: gname) (h: Z) (s: loc) (succ: node_rep), 
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (is_array (node_next pred) h)
          ∗
          ⌜ lvl < h ⌝
          ∗
          P pred
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s 
            ∗ 
            P pred 
            -∗ 
              list_equiv ([head] ++ L) P).
    Proof.
      iIntros (Hin) "Hlist".
      iRevert (head Hin) "Hlist".
      iInduction L as [|succ L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
      iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist".
      + iDestruct "Hlist" as (γ h s) "(Hpt & #Hs & #Hlock & Hh & HP & Hlist)".
        destruct L as [|next L]; subst.
        - iDestruct "Hlist" as (γ' h' t) "(Hpt' & #Ht & #Hlock' & #Hh')".
          iExists γ', h', t, tail. iFrame "# ∗".
          iSplit; first by iRight.
          iIntros "(Hpt' & HP)". 
          iExists γ, h, s. iFrame "# ∗".
          iExists γ', h', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ' h' n) "(Hpt' & #Hn & #Hlock' & #Hh' & Hmatch)".
          iExists γ', h', n, next. iFrame "# ∗".
          iSplit; first by iLeft; iRight; iLeft.
          iIntros "(Hpt' & HP)". 
          iExists γ, h, s. iFrame "# ∗".
          iExists γ', h', n. iFrame "# ∗".
      + iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof ("IHL" with "Hin") as "Himp'".
        iPoseProof ("Himp'" with "Hlist") as "Hlist".
        iDestruct "Hlist" as (γ h n next) "(%Hnext & Hpt & #Hn & #Hlock & #Hh & HP & Himp')".
        iExists γ, h, n, next. iFrame "# ∗".
        iSplit.
        { iPureIntro; destruct Hnext; first left; by right. }
        iIntros "(Hpt & HP)". 
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert (L: list node_rep) (head pred: node_rep) 
      (P: node_rep → iProp Σ) :
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        ∃ (γ: gname) (h: Z) (s: loc) (succ: node_rep),
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (is_array (node_next pred) h)
          ∗
          ⌜ lvl < h ⌝
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s -∗ list_equiv ([head] ++ L) P).
    Proof.
      intros Hin; destruct Hin as [Heq|Hin]; first subst.
      + iIntros "Hlist". destruct L as [|next L].
        - iDestruct "Hlist" as (γ h t) "(Hpt & #Ht & #Hlock & #Hh)".
          iExists γ, h, t, tail. iFrame "# ∗".
          iSplit; first by iRight.
          iIntros "Hpt". 
          iExists γ, h, t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ h n) "(Hpt & #Hn & #Hlock & #Hh & ?)".
          iExists γ, h, n, next. iFrame "# ∗".
          iSplit; first by repeat iLeft.
          iIntros "Hpt". 
          iExists γ, h, n. iFrame "# ∗".
      + iIntros "Hlist".
        iPoseProof (list_equiv_invert_L with "Hlist") as "Hlist"; first done.
        iDestruct "Hlist" as (γ h s succ) "(? & ? & ? & ? & ? & ? & Himp)".
        iExists γ, h, s, succ. iFrame.
        iIntros "?". iApply "Himp". iFrame.
    Qed.

    Lemma list_equiv_insert (s n: loc) (head pred new succ: node_rep) 
      (L: list node_rep) (γ': gname) (h': Z) (P: node_rep → iProp Σ) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        s ↦□ rep_to_node succ
        ∗ 
        (node_next pred +ₗ lvl) ↦{#1/2} #s
        ∗ 
        (node_next new +ₗ lvl) ↦{#1/2} #s
        ∗
        n ↦□ rep_to_node new
        ∗ 
        is_lock γ' (node_lock new) (is_array (node_next new) h')
        ∗
        ⌜ lvl < h' ⌝
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
      iIntros (Hnew Hrange Hsort Hin) .
      iIntros "Hlist (Hs & Hpt & Hpt' & Hn & Hlock' & Hh' & HP')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L HeqL' Hsort Hin) "Hlist Hs Hpt Hpt' Hn Hlock' Hh' HP'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L Hfalse); inversion Hfalse. }

      iIntros (head L HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist #Hs Hpt Hpt' #Hn #Hlock' Hh' HP'".
        destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ h t) "(Hpt'' & #Ht & #Hlock & Hh)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          assert (s = t) as -> by congruence.
          iDestruct (mapsto_agree with "Hs Ht") as %->%rep_to_node_inj.
          
          iExists (new :: nil), nil, nil.
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor; auto.
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ, h, n. iFrame "# ∗".
          iExists γ', h', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ h s') "(Hpt'' & #Hs' & #Hlock & Hh & Hmatch)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          assert (s = s') as <- by congruence.
          iDestruct (mapsto_agree with "Hs Hs'") as %<-%rep_to_node_inj.

          iExists (new :: succ :: L), nil, (L ++ [tail]).
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro.
            repeat apply Sorted_inv in Hsort as (Hsort&?).
            repeat econstructor; auto. 
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ, h, n. iFrame "# ∗".
          iExists γ', h', s. iFrame "# ∗".
      + destruct L as [|next L]; first by inversion HinL.
        iIntros "Hlist #Hs Hpt Hpt' #Hn #Hlock' Hh' HP'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (γ h x) "(Hpt'' & #Hx & Hlock & Hh & HP & Hmatch)".
        iPoseProof ("IHL'" $! next L with "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$] [$]") 
          as "Hclose"; auto.
        
        iDestruct "Hclose" as (L' L1 L2) "(Hpt' & %Hsplit & %Hsort' & %Hperm' & Himp')".
        iExists (next :: L'), (head :: L1), L2. iFrame.
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

        iIntros "Hpt". iExists γ, h, x.
        iPoseProof ("Himp'" with "Hpt") as "Hlist".
        iFrame "# ∗".
    Qed.

  End Proofs.
End ListEquiv.