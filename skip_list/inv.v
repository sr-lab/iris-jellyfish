From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_lt node_rep code key_equiv.


Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_nr_F_inG :> inG Σ (frac_authR (gsetUR node_rep));
  gset_Z_disj_inG :> inG Σ (gset_disjUR Z)
}.

Local Open Scope Z.
Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module NodeLt := NodeLt Params.
  Export NodeLt.

  Record lazy_gname := mk_lazy_gname {
    s_auth: gname;
    s_frac: gname;
    s_tok: gname
  }.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, lockG Σ} (N : namespace).

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

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

        | succ :: _ => ∃ (l: loc) (γ: gname), 
                       ⌜ node_next pred = Some l ⌝
                       ∗
                       l ↦{#1 / 2} rep_to_node succ
                       ∗
                       is_lock γ (node_lock pred) (node_inv l)
                       ∗
                       list_equiv succs
        end
      end.

    Definition lazy_list_inv (head: node_rep) (S: gset node_rep) : iProp Σ := 
      ∃ (L: list node_rep),
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      ⌜ node_key head = INT_MIN ⌝
      ∗
      list_equiv ([head] ++ L)
    .

    Fixpoint skip_list_equiv (head: node_rep) (lvl: Z) (L: list (list node_rep)) (S St: gset node_rep) : iProp Σ :=
      match L with
      | nil => True
      | top :: bots =>
        match bots with
        | nil => ⌜ St = S ⌝
                 ∗
                 inv (levelN lvl) (lazy_list_inv head St)
                 ∗
                 ⌜ node_down head = None ⌝
                 ∗
                 ⌜ lvl = 0 ⌝
                 
        | _ :: _ => ∃ (Sb: gset node_rep) (l: loc) (down: node_rep),
                    ⌜ St ⊆ Sb ⊆ S ⌝
                    ∗
                    inv (levelN lvl) (lazy_list_inv head St)
                    ∗
                    ⌜ node_down head = Some l ⌝
                    ∗
                    l ↦ rep_to_node down
                    ∗
                    skip_list_equiv down (lvl - 1) bots S Sb
        end
      end.

    Definition skip_list_inv (head: node_rep) (S: gset node_rep) : iProp Σ := 
      ∃ (St: gset node_rep) (L: list (list node_rep)),
      ⌜ St ⊆ S ⌝
      ∗
      skip_list_equiv head MAX_HEIGHT L S St
    .

    Definition is_skip_list (v: val) (Skeys: gset Z) : iProp Σ := 
      ∃ (l:loc) (head: node_rep) (S: gset node_rep),
      ⌜ key_equiv S Skeys ⌝
      ∗
      ⌜ #l = v ⌝
      ∗
      l ↦ rep_to_node head
      ∗
      inv N (skip_list_inv head S).
    

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

    Lemma list_equiv_insert (head pred new succ: node_rep)
      (L: list node_rep) (l l': loc) (γ': gname) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) ⊢ 
        ⌜ node_next pred = Some l ⌝ ∗ l↦{#1/2} rep_to_node succ 
        ∗ 
        ⌜ node_next new = Some l' ⌝ ∗ l'↦{#1/2} rep_to_node succ
        ∗
        is_lock γ' (node_lock new) (node_inv l') -∗ 
          ∃ (L': list node_rep), 
            l ↦ rep_to_node succ 
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
      iIntros (Hin); inversion Hin.
      * subst.
        iIntros "Hlist %Hsome Hpt %Hsome' Hpt' #Hlock'".
        iExists (new :: L).
        destruct L as [|].
        ** simpl.
           iDestruct "Hlist" as (l'' γ) "(%Hsome'' & Hpt'' & #Hlock)".
           assert (l = l'') as <- by congruence.
           iDestruct (mapsto_agree with "Hpt Hpt''") as %->.

           iFrame. iSplit.
           { 
             iPureIntro; apply Sorted_cons; auto.
             econstructor; unfold node_lt; lia.
           }
           iSplit; first auto.
           iIntros "Hpt". iExists _, _.
           iFrame "# ∗". iSplit; first done.
           iExists _, _. by iFrame "# ∗".
        ** iDestruct "Hlist" as (l'' γ) "(%Hsome'' & Hpt'' & #Hlock & Hmatch)".
           assert (l = l'') as <- by congruence.
           iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
           apply rep_to_node_inj in Heq; subst.

           iFrame. iSplit.
           { 
             iPureIntro. simpl in Hsort.
             repeat apply Sorted_inv in Hsort as (Hsort&?).
             repeat econstructor; auto. 
             all: unfold node_lt; lia.
           }
           iSplit; first auto.
           iIntros "Hpt". iExists _, _.
           iFrame "# ∗". iSplit; first done.
           iExists _, _. by iFrame "# ∗".
      * destruct L as [|head' L]; first by inversion H0.
        iIntros "Hlist %Hsome Hpt %Hsome' Hpt' #Hlock'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (l'' γ) "(Hsome'' & Hpt'' & Hlock & Hmatch)".
        iPoseProof ("IHL'" $! head' L with "[%] [%] [%] [$] [%] [$] [%] [$] [$]") 
          as "Hclose"; auto.
        
        iDestruct "Hclose" as (L') "(Hpt' & %Hsort' & %Hperm' & Himp')".
        iExists (head' :: L'). iFrame.
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
End SkipListInv.