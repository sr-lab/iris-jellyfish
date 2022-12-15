From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import cmra auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jelly_fish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.


Local Open Scope Z.

Class skipGS Σ := SkipGS {
  frac_gmapR :> inG Σ (frac_authR (gmapUR Z (arg_maxUR Z)));
  auth_gsetR :> inG Σ (authR (gsetUR node_rep));
  auth_toksR :> inG Σ (authR (gset_disjUR Z))
}.

Record sub_gname := mk_sub_gname {
  s_auth: gname;
  s_toks: gname
}.

Record bot_gname := mk_bot_gname {
  s_frac: gname
}.

Module ListEquiv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module SkipList := SkipList Params.
  Export SkipList.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ} (lvl: Z) (osub: option sub_gname).

    Definition is_node (rep: node_rep) (v: val_rep) : iProp Σ :=
      match osub with
      | Some bot => own (s_auth bot) (◯ {[ rep ]})
                    ∗
                    own (s_toks bot) (◯ GSet {[ node_key rep ]})
                    
      | None => (node_val rep) ↦{#1 / 2} rep_to_val v
      end.

    Definition is_val (oM: option (gmap Z (argmax Z))) (rep: node_rep) (v: val_rep) : Prop :=
      match oM with
      | Some M => ∃ (vs: gset Z), 
                    M !! (node_key rep) = Some (prodZ vs (val_ts v))
                    ∧
                    val_v v ∈ vs
      | None => True
      end.

    Definition locked_val (s: loc) : iProp Σ := 
      match osub with
      | Some _ => True
      | None => ∃ (succ: node_rep),
                  s ↦□ rep_to_node succ
                  ∗
                  (⌜ succ = tail ⌝ ∨
                  ∃ (v: val_rep), (node_val succ) ↦{#1 / 2} rep_to_val v)
      end.

    Definition in_lock (rep: node_rep) : iProp Σ := 
      ∃ (s: loc), 
        (node_next rep +ₗ lvl) ↦{#1 / 2} #s 
        ∗ 
        locked_val s.

    Definition opt_lookup (oM: option (gmap Z (argmax Z))) (k: Z) : option (argmax Z) := 
      match oM with
      | Some M => M !! k
      | None => None
      end.

    Definition opt_insert (oM: option (gmap Z (argmax Z))) (k: Z) (v: argmax Z) : option (gmap Z (argmax Z)) :=
      match oM with
      | Some M => Some (<[k := v]>M)
      | None => None
      end.

    Definition opt_delete (oM: option (gmap Z (argmax Z))) (k: Z) : option (gmap Z (argmax Z)) :=
      match oM with
      | Some M => Some (delete k M)
      | None => None
      end.

    Fixpoint list_equiv (L: list node_rep) (oM: option (gmap Z (argmax Z))) : iProp Σ :=
      match L with
      | nil => True
      | pred :: succs => 
        match succs with
        | nil => ∃ (γ: gname) (l: val) (t: loc), 
                  (node_next pred +ₗ lvl) ↦{#1 / 2} #t
                  ∗
                  t ↦□ rep_to_node tail
                  ∗
                  (node_locks pred +ₗ lvl) ↦□ l
                  ∗
                  is_lock γ l (in_lock pred)

        | succ :: _ => ∃ (v: val_rep) (γ: gname) (l: val) (s: loc), 
                        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
                        ∗
                        s ↦□ rep_to_node succ
                        ∗
                        (node_locks pred +ₗ lvl) ↦□ l
                        ∗
                        is_lock γ l (in_lock pred)
                        ∗
                        is_node succ v
                        ∗
                        ⌜ is_val oM succ v ⌝
                        ∗
                        list_equiv succs (opt_delete oM (node_key succ))
        end
      end. 
    

    Lemma list_equiv_cons (pred: node_rep) (L: list node_rep) 
      (oM: option (gmap Z (argmax Z))) :
      list_equiv (pred :: L) oM ⊢ 
        ∃ (succ: node_rep), 
          ( list_equiv L (opt_delete oM (node_key succ))
            ∗ 
            (list_equiv L (opt_delete oM (node_key succ)) -∗ list_equiv (pred :: L) oM)).
    Proof.
      destruct L as [|succ].
      + iIntros "Hrep". by iFrame.
      + iIntros "Hlist". 
        iDestruct "Hlist" as (v γ l s) "(Hpt & Hs & Hl & Hlock & Hnode & Hval & Hmatch)".
        iExists succ. iFrame.
        iIntros "Hlist". iFrame.
        iExists v, γ, l, s. iFrame.
    Qed.

    Lemma list_equiv_join (s: loc) (head pred succ: node_rep) (L: list node_rep) 
      (oM: option (gmap Z (argmax Z))) :
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) oM ⊢
        (node_next pred +ₗ lvl) ↦{#1/2} #s
        ∗ 
        s ↦□ rep_to_node succ
        -∗
          ∃ (L1 L2: list node_rep), 
            ⌜ [head] ++ L ++ [tail] = L1 ++ [pred; succ] ++ L2 ⌝
            ∗
            (node_next pred +ₗ lvl) ↦{#1/2} #s
            ∗ 
            list_equiv ([head] ++ L) oM.
    Proof.
      iIntros (Hsort Hin) "Hlist (Hnext & #Hs)".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head oM L HeqL' Hsort Hin) "Hlist".
      iInduction L' as [|head' L'] "IHL".
      { iIntros (head oM L Hfalse); inversion Hfalse. }

      iIntros (head oM L HeqL' Hsort Hin) "Hlist".
      inversion HeqL'; subst.
      destruct Hin as [Heq|Hin].
      + subst.
        destruct L as [|pred' L].
        - iDestruct "Hlist" as (γ l t) "(Hnext' & #Ht & Hlocks & #Hlock)".
          iDestruct (mapsto_agree with "Hnext Hnext'") as %Ht.
          inversion Ht; subst.
          iDestruct (mapsto_agree with "Hs Ht") as %->%rep_to_node_inj.
          iExists nil, nil.
          iSplit; first done. iFrame.
          iExists γ, l, t. iFrame "# ∗".
        - iDestruct "Hlist" as (v γ l s') "(Hnext' & #Hs' & #Hl & #Hlock & Hnode & #Hval & Hmatch)".
          iDestruct (mapsto_agree with "Hnext Hnext'") as %Hs.
          inversion Hs; subst.
          iDestruct (mapsto_agree with "Hs Hs'") as %->%rep_to_node_inj.
          iExists nil, (L ++ [tail]).
          iSplit; first done. iFrame.
          iExists v, γ, l, s'. iFrame "# ∗".
      + destruct L as [|pred' L]; first inversion Hin.
        iPoseProof ("IHL" with "Hnext") as "IHL'".
        iPoseProof (list_equiv_cons with "Hlist") as "Hlist".
        iDestruct "Hlist" as (succ') "(Hlist & Himp)".
        iPoseProof ("IHL'" $! pred' with "[%] [%] [%] [$]") as (L1 L2) "(%Heq & Hnext & Hlist)".
        { done. }
        { 
          apply node_rep_sorted_app in Hsort as [_ Hsort].
          rewrite -app_ass //.
        }
        { done. }

        iPoseProof ("Himp" with "Hlist") as "Hlist".
        iExists (head :: L1), L2. iFrame.
        iPureIntro; simpl in *.
        rewrite Heq //.
    Qed.

    Lemma list_equiv_split (pred succ: node_rep) (L L1 L2: list node_rep) 
      (oM: option (gmap Z (argmax Z))) :
      L ++ [tail] = L1 ++ [pred; succ] ++ L2 →
      list_equiv L oM ⊢ 
        ∃ (s: loc),
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          ((node_next pred +ₗ lvl) ↦{#1 / 2} #s -∗ list_equiv L oM).
    Proof.
      revert L oM. induction L1 => L oM HL.
      + destruct L as [|curr L].
        { exfalso. inversion HL. }
        inversion HL as [[H0 HL']]; subst.
        destruct L as [|curr L].
        - inversion HL'; subst.
          iIntros "Hlist".
          iDestruct "Hlist" as (γ l t) "(Hpt & #Ht & #Hl & #Hlock)".
          iExists t. iFrame "# ∗".
          iIntros "Hpt". 
          iExists γ, l, t. iFrame "# ∗".
        - inversion HL'; subst.
          iIntros "Hlist". 
          iDestruct "Hlist" as (v γ l s) "(Hpt & #Hs & #Hl & #Hlock & Hnode & #Hval & Hmatch)".
          iExists s. iFrame "# ∗".
          iIntros "Hpt". 
          iExists v, γ, l, s. iFrame "# ∗".
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
        iPoseProof (list_equiv_cons with "Hlist") as "Hlist".
        iDestruct "Hlist" as (?) "(Hlist & Himp)".
        iPoseProof (IHL1 with "Hlist") as "Hlist"; auto.
        iDestruct "Hlist" as (s) "(Hpt & #Hs & Himp')".
        iExists s. iFrame "# ∗".
        iIntros "Hpt".
        iApply "Himp". iApply "Himp'". iFrame.
    Qed.

    Lemma list_equiv_invert_L (L: list node_rep) (head pred: node_rep) 
      (oM: option (gmap Z (argmax Z))) :
      In pred L →
      list_equiv ([head] ++ L) oM ⊢ 
        ∃ (v: val_rep) (γ: gname) (l: val) (s: loc) (succ: node_rep), 
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          (node_locks pred +ₗ lvl) ↦□ l
          ∗
          is_lock γ l (in_lock pred)
          ∗
          is_node pred v
          ∗
          ⌜ is_val oM pred v ⌝
          ∗
          ∀ (S: gset Z) (v': val_rep),
            (node_next pred +ₗ lvl) ↦{#1/2} #s 
            ∗
            is_node pred v'
            ∗
            ⌜ val_v v' ∈ S ⌝
            -∗ 
              list_equiv ([head] ++ L) (opt_insert oM (node_key pred) (prodZ S (val_ts v'))).
    Proof.
      iIntros (Hin) "Hlist".
      iRevert (head oM Hin) "Hlist".
      iInduction L as [|succ L] "IHL"; iIntros (head oM) "Hin"; first by iExFalso.
      iDestruct "Hin" as "[%Heq|Hin]"; subst; iIntros "Hlist".
      + iDestruct "Hlist" as (v γ l s) "(Hpt & #Hs & #Hl & #Hlock & Hnode & Hval & Hlist)".
        destruct L as [|next L]; subst.
        - iDestruct "Hlist" as (γ' l' t) "(Hpt' & #Ht & #Hl' & #Hlock')".
          iExists v, γ', l', t, tail.
          iFrame "# ∗". iSplit; first by iRight.

          iIntros (S v') "(Hpt' & Hnode & %Hval)". 
          iExists v', γ, l, s. iFrame "# ∗".
          iSplit.
          {
            destruct oM as [M|]; last done.
            iExists S; rewrite lookup_insert //.
          }
          iExists γ', l', t. iFrame "# ∗".
        - iDestruct "Hlist" as (v' γ' l' n) "(Hpt' & #Hn & #Hl' & #Hlock' & Hnode' & Hval' & Hmatch)".
          iExists v, γ', l', n, next.
          iFrame "# ∗". iSplit; first by iLeft; iRight; iLeft.
          
          iIntros (S v'') "(Hpt' & Hnode & %Hval)". 
          iExists v'', γ, l, s. iFrame "# ∗".

          destruct oM as [M|].
          * iSplit.
            { iExists S; rewrite lookup_insert //. }
            iExists v', γ', l', n. rewrite /= delete_insert_delete. iFrame "# ∗".
          * iSplit; first done.
            iExists v', γ', l', n. iFrame "# ∗".
      + iDestruct "Hlist" as (v γ l s) "(Hnext & #Hs & #Hl & #Hlock & Hnode & %Hval & Hlist)".
        iPoseProof ("IHL" with "Hin Hlist") as "Hlist".

        iDestruct "Hlist" as (v' γ' l' s' succ') "(%Hsucc' & Hnext' & #Hs' & #Hl' & #Hlock' & Hnode' & %Hval' & Himp)".
        iExists v', γ', l', s', succ'. iFrame "# ∗".
        iSplit.
        { iPureIntro; destruct Hsucc'; first left; by right. }
        iSplit.
        {
          iPureIntro. 
          destruct oM as [M|]; last done.
          simpl in *.
          destruct Hval as [vs [Hsome Hin]]; destruct Hval' as [vs' [Hsome' Hin']].
          exists vs'. split; last done.
          rewrite lookup_delete_Some in Hsome'.
          by destruct Hsome' as [_ Hsome'].
        }

        iIntros (S v'') "(Hpt'' & Hnode'' & %Hval'')".
        iPoseProof ("Himp" $! S v'' with "[Hpt'' Hnode'']") as "Hlist".
        { by iFrame. }
        iExists v, γ, l, s. 
        destruct oM as [M|]; last iFrame "# ∗".
        destruct Hval as [vs [Hsome Hin]].
        destruct Hval' as [vs' [Hsome' Hin']].
        rewrite lookup_delete_Some in Hsome'.
        destruct Hsome' as [Hne Hsome'].
        rewrite /= delete_insert_ne // lookup_insert_ne //.
        iFrame "# ∗". by iExists vs.
    Qed.

    Lemma list_equiv_invert (L: list node_rep) (head pred: node_rep) 
      (oM: option (gmap Z (argmax Z))) :
      pred = head ∨ In pred L →
      list_equiv ([head] ++ L) oM ⊢ 
        ∃ (γ: gname) (l: val) (s: loc) (succ: node_rep),
          (⌜ In succ L ⌝ ∨ ⌜ succ = tail ⌝)
          ∗
          (node_next pred +ₗ lvl) ↦{#1/2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          (node_locks pred +ₗ lvl) ↦□ l
          ∗
          is_lock γ l (in_lock pred)
          ∗
          ((node_next pred +ₗ lvl) ↦{#1/2} #s -∗ list_equiv ([head] ++ L) oM).
    Proof.
      intros Hin; destruct Hin as [Heq|Hin]; first subst.
      + iIntros "Hlist". destruct L as [|next L].
        - iDestruct "Hlist" as (γ l t) "(Hpt & #Ht & #Hl & #Hlock)".
          iExists γ, l, t, tail. iFrame "# ∗".
          iSplit; first by iRight.
          iIntros "Hpt". 
          iExists γ, l, t. iFrame "# ∗".
        - iDestruct "Hlist" as (v γ l n) "(Hpt & #Hn & #Hl & #Hlock & ?)".
          iExists γ, l, n, next. iFrame "# ∗".
          iSplit; first by repeat iLeft.
          iIntros "Hpt". 
          iExists v, γ, l, n. iFrame "# ∗".
      + iIntros "Hlist".
        iPoseProof (list_equiv_invert_L with "Hlist") as "Hlist"; first done.
        iDestruct "Hlist" as (? γ l s succ) "(? & ? & ? & ? & ? & Hnode & %Hval & Himp)".
        iExists γ, l, s, succ. iFrame.
        iIntros "Hnext". 

        destruct oM as [M|].
        - destruct Hval as [vs [Hsome Hvs]].
          iPoseProof ("Himp" $! vs v with "[Hnext Hnode]") as "Hlist".
          { by iFrame. }
          rewrite /opt_insert insert_id //.
        - iApply ("Himp" $! {[ val_v v ]} v). iFrame. 
          rewrite elem_of_singleton //.
    Qed.

    Lemma list_equiv_insert (s n: loc) (head pred new succ: node_rep) (L: list node_rep) 
      (v': val_rep) (γ': gname) (l': val) (oM: option (gmap Z (argmax Z))) :
      node_key new < node_key tail →
      node_key pred < node_key new < node_key succ →
      Sorted node_lt ([head] ++ L ++ [tail]) →
      pred = head ∨ In pred L →
      opt_lookup oM (node_key new) = None →
      list_equiv ([head] ++ L) oM ⊢ 
        s ↦□ rep_to_node succ
        ∗ 
        (node_next pred +ₗ lvl) ↦{#1/2} #s
        ∗ 
        (node_next new +ₗ lvl) ↦{#1/2} #s
        ∗
        n ↦□ rep_to_node new
        ∗
        (node_locks new +ₗ lvl) ↦□ l'
        ∗
        is_lock γ' l' (in_lock new)
        ∗
        is_node new v'
        -∗ 
          ∃ (L': list node_rep), 
            (node_next pred +ₗ lvl) ↦ #s
            ∗
            ⌜ Sorted node_lt ([head] ++ L' ++ [tail]) ⌝
            ∗
            ⌜ Permutation ([head] ++ L') ([head; new] ++ L) ⌝ 
            ∗
            ((node_next pred +ₗ lvl) ↦{#1/2} #n 
              -∗ 
                list_equiv ([head] ++ L') (opt_insert oM (node_key new) (prodZ {[val_v v']} (val_ts v')))).
    Proof.
      iIntros (Hnew Hrange Hsort Hin Hnone).
      iIntros "Hlist (Hs & Hpt & Hpt' & Hn & Hl' & Hlock' & Hnode')".
      remember ([head] ++ L) as L' eqn:HeqL'.
      rewrite -in_inv in Hin.

      iRevert (head L oM HeqL' Hsort Hin Hnone) "Hlist Hs Hpt Hpt' Hn Hl' Hlock' Hnode'".
      iInduction L' as [|pred'] "IHL'".
      { iIntros (head L oM Hfalse); inversion Hfalse. }

      iIntros (head L oM HeqL' Hsort).
      inversion HeqL'; subst.
      iIntros (Hin Hnone); inversion Hin as [Heq|HinL].
      + subst.
        iIntros "Hlist #Hs Hpt Hpt' #Hn #Hl' #Hlock' Hnode'".
        destruct L as [|succ' L].
        - iDestruct "Hlist" as (γ l t) "(Hpt'' & #Ht & #Hl & #Hlock)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          assert (s = t) as -> by congruence.
          iDestruct (mapsto_agree with "Hs Ht") as %->%rep_to_node_inj.
          
          iExists (new :: nil).
          iFrame. iSplit.
          { 
            iPureIntro; apply Sorted_cons; econstructor; auto.
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists v', γ, l, n. iFrame "# ∗".
          iSplit.
          {
            destruct oM as [M|]; last done.
            iPureIntro; exists {[val_v v']}.
            split; last rewrite elem_of_singleton //.
            rewrite lookup_insert //.
          }
          iExists γ', l', t. iFrame "# ∗".
        - iDestruct "Hlist" as (v γ l s') "(Hpt'' & #Hs' & #Hl & #Hlock & Hnode & #Hval & Hmatch)".
          iDestruct (mapsto_agree with "Hpt Hpt''") as %Heq.
          assert (s = s') as <- by congruence.
          iDestruct (mapsto_agree with "Hs Hs'") as %<-%rep_to_node_inj.

          iExists (new :: succ :: L).
          iFrame. iSplit.
          { 
            iPureIntro.
            repeat apply Sorted_inv in Hsort as (Hsort&?).
            repeat econstructor; auto. 
            all: unfold node_lt; lia.
          }
          iSplit; first auto.
          iIntros "Hpt". 
          iExists v', γ, l, n. iFrame "# ∗".
          iSplit.
          {
            destruct oM as [M|]; last done.
            iPureIntro; exists {[val_v v']}.
            split; last rewrite elem_of_singleton //.
            rewrite lookup_insert //.
          }
          iExists v, γ', l', s.
          destruct oM as [M|]; last iFrame "# ∗".
          rewrite /= delete_insert; last done.
          iFrame "# ∗".
      + destruct L as [|next L]; first by inversion HinL.
        iIntros "Hlist #Hs Hpt Hpt' #Hn #Hl' #Hlock' Hnode'".

        simpl in Hsort; apply Sorted_inv in Hsort as (Hsort&Hhd).
        iDestruct "Hlist" as (v γ l x) "(Hpt'' & #Hx & #Hl & #Hlock & Hnode & %Hval & Hmatch)".
        iPoseProof ("IHL'" $! next L with "[%] [%] [%] [%] [$] [$] [$] [$] [$] [$] [$] [$]") 
          as "Hclose"; auto.
        { 
          destruct oM as [M|]; last done.
          simpl in *; destruct Hval as [S [Hsome Hval]].
          rewrite lookup_delete_ne //.
          apply (lookup_ne M); rewrite Hsome Hnone //.
        }
        
        iDestruct "Hclose" as (L') "(Hpt' & %Hsort' & %Hperm' & Himp')".
        iExists (next :: L'). iFrame.
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

        iIntros "Hpt". iExists v, γ, l, x.
        iPoseProof ("Himp'" with "Hpt") as "Hlist".
        destruct oM as [M|]; last iFrame "# ∗".
        simpl in *; destruct Hval as [S [Hsome Hval]].
        assert (node_key next ≠ node_key new) as Hne.
        { apply (lookup_ne M); rewrite Hsome Hnone //. }

        rewrite delete_insert_ne; last first. 
        { apply (lookup_ne M); rewrite Hsome Hnone //. }
        iFrame "# ∗"; iPureIntro.
        exists S. rewrite lookup_insert_ne //.
    Qed.

  End Proofs.
End ListEquiv.