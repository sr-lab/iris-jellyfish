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

    Definition nodeN (l: loc) := nroot .@ "node" .@ l.

    Definition node_inv(s: loc) (succ: node_rep) : iProp Σ := 
      s ↦{#1 / 2} rep_to_node succ.

    Fixpoint exp2 (n: nat) : frac :=
      match n with
      | O => 1
      | S n => 2 * exp2 n
      end.

    Definition lfrac : frac := 1 / exp2 (Z.to_nat (lvl + 2)).

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
                 inv (nodeN t) (node_inv t tail)
                 ∗
                 t ↦{#lfrac} rep_to_node tail
                 ∗
                 is_lock γ (node_lock pred) (in_lock (node_next pred))

        | succ :: _ => ∃ (γ: gname) (s: loc), 
                       (node_next pred +ₗ lvl) ↦{#1 / 2} #s
                       ∗
                       inv (nodeN s) (node_inv s succ)
                       ∗
                       s ↦{#lfrac} rep_to_node succ
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
      + iIntros "Hlist". 
        iDestruct "Hlist" as (γ s) "(Hpt & Hinvs & Hs & Hlock & HP & Hmatch)".
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
          inv (nodeN s) (node_inv s succ)
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
          iDestruct "Hlist" as (γ t) "(Hpt & #Hinvt & Ht & #Hlock)".
          iExists γ, t. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, t. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (γ s) "(Hpt & #Hinvs & Hs & #Hlock & Hmatch)".
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
        iDestruct "Hlist" as (γ s) "(Hpt & #Hinvs & Hlock & Himp')".
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
          inv (nodeN s) (node_inv s succ)
          ∗
          s ↦{#lfrac} rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          P pred
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s 
            ∗ 
            s ↦{#lfrac} rep_to_node succ
            ∗ 
            P pred 
            -∗ 
              list_equiv ([head] ++ L) P).
    Proof.
      iIntros (Hin) "Hlist".
      iRevert (head Hin) "Hlist".
      iInduction L as [|succ L] "IHL"; iIntros (head) "Hin"; first by iExFalso.
      iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist".
      + iDestruct "Hlist" as (γ s) "(Hpt & #Hinvs & Hs & #Hlock & HP & Hlist)".
        destruct L as [|next L]; subst.
        - iDestruct "Hlist" as (γ' t) "(Hpt' & #Hinvt & Ht & #Hlock')".
          iExists t, tail, [head], nil, γ'. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "(Hpt' & Hs' & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ' n) "(Hpt' & #Hinvs' & Hn & #Hlock' & Hmatch)".
          iExists n, next, [head], (L ++ [tail]), γ'. iFrame "# ∗".
          iSplit; first by iLeft; iRight; iLeft. iSplit; first done.
          iIntros "(Hpt' & Hn' & HP)". 
          iExists γ, s. iFrame "# ∗".
          iExists γ', n. iFrame "# ∗".
      + iPoseProof (list_equiv_cons with "Hlist") as "(Hlist & Himp)".
        iPoseProof ("IHL" with "Hin") as "Himp'".
        iPoseProof ("Himp'" with "Hlist") as "Hlist".
        iDestruct "Hlist" as (n next L1 L2 γ) "(%Hnext & %Hsplit & Hpt & #Hinvn & Hn & #Hlock & HP & Himp')".
        iExists n, next, ([head] ++ L1), L2, γ. iFrame "# ∗".
        iSplit.
        { iPureIntro; destruct Hnext; first left; by right. }
        iSplit.
        { iPureIntro; simpl in *; by rewrite Hsplit. }
        iIntros "(Hpt & Hn & HP)". 
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
          inv (nodeN s) (node_inv s succ)
          ∗
          s ↦{#lfrac} rep_to_node succ
          ∗ 
          is_lock γ (node_lock pred) (in_lock (node_next pred))
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s 
            ∗ 
            s ↦{#lfrac} rep_to_node succ
            -∗ 
              list_equiv ([head] ++ L) P).
    Proof.
      intros Hin; destruct Hin as [Heq|Hin]; first subst.
      + iIntros "Hlist". destruct L as [|next L].
        - iDestruct "Hlist" as (γ t) "(Hpt & #Hinvt & Ht & #Hlock)".
          iExists t, tail, nil, nil, γ. iFrame "# ∗".
          iSplit; first by iRight. iSplit; first done.
          iIntros "(Hpt & Ht)". 
          iExists γ, t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ n) "(Hpt & #Hinvn & Hn & #Hlock & ?)".
          iExists n, next, nil, (L ++ [tail]), γ. iFrame "# ∗".
          iSplit; first by repeat iLeft. iSplit; first done.
          iIntros "(Hpt & Hn)". 
          iExists γ, n. iFrame "# ∗".
      + iIntros "Hlist".
        iPoseProof (list_equiv_invert_L with "Hlist") as "Hlist"; first done.
        iDestruct "Hlist" as (s succ L1 L2 γ) "(? & ? & ? & ? & ? & ? & ? & Himp)".
        iExists s, succ, L1, L2, γ. iFrame.
        iIntros "(? & ?)". iApply "Himp". iFrame.
    Qed.

    Lemma list_equiv_insert (s n: loc) (head pred new succ: node_rep) 
      (L: list node_rep) (γ': gname) (P: node_rep → iProp Σ) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) P ⊢ 
        s ↦{#lfrac} rep_to_node succ
        ∗ 
        (node_next pred +ₗ lvl) ↦{#1/2} #s
        ∗ 
        (node_next new +ₗ lvl) ↦{#1/2} #s
        ∗
        inv (nodeN n) (node_inv n new)
        ∗ 
        n ↦{#lfrac} rep_to_node new
        ∗ 
        is_lock γ' (node_lock new) (in_lock (node_next new))
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
      iIntros "Hlist (Hs & Hpt & Hpt' & Hinvn & Hn & Hlock' & HP')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L HeqL' Hsort Hin) "Hlist Hs Hpt Hpt' Hinvn Hn Hlock' HP'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L Hfalse); inversion Hfalse. }

      iIntros (head L HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist Hs Hpt Hpt' #Hinvn Hn #Hlock' HP'".
        destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ t) "(Hpt'' & #Hinvt & Ht & #Hlock)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          assert (s = t) as -> by congruence.
          iDestruct (mapsto_agree with "Hs Ht") as %->%rep_to_node_inj.
          
          iExists (new :: nil), nil, nil.
          iFrame. iSplit; first done. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor.
            auto. econstructor.
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists γ, n. iFrame "# ∗".
          iExists γ', t. iFrame "# ∗".
        - iDestruct "Hlist" as (γ s') "(Hpt'' & #Hinvs' & Hs' & #Hlock & Hmatch)".
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
          iExists γ, n. iFrame "# ∗".
          iExists γ', s. iFrame "# ∗".
      + destruct L as [|head' L]; first by inversion HinL.
        iIntros "Hlist Hs Hpt Hpt' #Hinvn Hn #Hlock' HP'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (γ h') "(Hpt'' & #Hinvh' & Hh' & Hlock & HP & Hmatch)".
        iPoseProof ("IHL'" $! head' L with "[%] [%] [%] [$] [$] [$] [$] [$] [$] [$] [$]") 
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
        iFrame "# ∗".
    Qed.

  End Proofs.
End ListEquiv.