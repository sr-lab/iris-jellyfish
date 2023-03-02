From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.heap_lang Require Import notation.
Import derived_laws_later.bi.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import proofmode lock.
From SkipList.jelly_fish Require Import code.


Definition tval : Type := Z * Z.

Class skipG Σ := SkipG { 
  skip_authG :> inG Σ (authR (gset node_rep));
  skip_disjG :> inG Σ (gset_disjR Z);
  skip_toksG :> inG Σ (authR (gset_disjR Z));
  skip_gmapG :> ghost_mapG Σ Z (tval * list tval)
}.

Record lazy_gname := mk_lazy_gname {
  auth_gname: gname;
  disj_gname: gname;
  toks_gname: gname
}.
(* Necessary to support total lookup (m !!! k) *)
Global Instance lazy_gname_inhabited : Inhabited lazy_gname := 
  populate (mk_lazy_gname inhabitant inhabitant inhabitant).

Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module SkipList := SkipList Params.
  Export SkipList.

  Section invariant.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    (* Successor chain *)
    Definition has_next (lvl: Z) (Γ: lazy_gname) (pred: node_rep) : iProp Σ :=
      ∃ (s: loc) (succ: node_rep), 
        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
        ∗
        own Γ.(disj_gname) (ZRange (node_key pred) (node_key succ)).

    (* Lock resources *)
    Definition locked_val (lvl: Z) (s: loc) : iProp Σ := 
      if decide (lvl = 0) then 
        (∃ (succ: node_rep), s ↦□ rep_to_node succ ∗
        (⌜ succ = tail ⌝ ∨ ∃ (val: val_rep), node_val succ ↦{#1 / 2} rep_to_val val))%I
      else True%I.
    Definition in_lock (lvl: Z) (pred: node_rep) : iProp Σ := 
      ∃ (s: loc), (node_next pred +ₗ lvl) ↦{#1 / 2} #s ∗ locked_val lvl s.
    Definition has_lock (lvl: Z) (pred: node_rep) : iProp Σ := 
      is_lock #(node_lock pred +ₗ lvl) (in_lock lvl pred).

    (* Sublist resources *)
    Definition has_sub (γ: lazy_gname) (node: node_rep) : iProp Σ :=
      own γ.(auth_gname) (◯ {[ node ]})
      ∗
      own γ.(toks_gname) (◯ GSet {[ node_key node ]}).

    (* Lazy list resources for a given level *)
    Definition lazy_list (head: node_rep) (S: gset node_rep)
      (Γ: lazy_gname) (γ: option lazy_gname) (lvl: Z) : iProp Σ :=
      own Γ.(auth_gname) (● S)
      ∗
      own Γ.(disj_gname) (GSet (set_map node_key S))
      ∗
      own Γ.(toks_gname) (● GSet (set_map node_key S))
      ∗
      ([∗ set] n ∈ {[head]} ∪ S, has_next lvl Γ n)
      ∗
      ([∗ set] n ∈ {[head]} ∪ S, has_lock lvl n)
      ∗
      match γ with None => True | Some γ => [∗ set] n ∈ S, has_sub γ n end.

    (* Vertical list resources *)
    Fixpoint vertical_list (vl: list tval) (p: loc) : iProp Σ := 
      match vl with
      | nil => ⌜ p = dummy_null ⌝
      | vt :: vl => ∃ (n: loc), p ↦□ rep_to_val (vt, n)%core ∗ vertical_list vl n
      end.
    Definition has_val (γ: gname) (node: node_rep) : iProp Σ :=
      ∃ (val: val_rep) (vl: list tval),
        node_val node ↦{#1 / 2} rep_to_val val
        ∗
        node_key node ↪[γ] (val_vt val, vl)
        ∗
        vertical_list vl (val_p val).

    (* JellyFish map resources *)
    Definition jf_map (head: node_rep) (S: gset node_rep) 
      (m: gmap Z (tval * list tval)) (Γ: lazy_gname) : iProp Σ :=
      lazy_list head S Γ None 0
      ∗
      ∃ (γ: gname),
        ⌜ dom m = set_map node_key S ⌝
        ∗
        ghost_map_auth γ 1 m
        ∗
        [∗ set] n ∈ S, has_val γ n.

    (* Skip list resources *)
    Definition is_lazy_list (head: node_rep) (Γ: lazy_gname)
      (γ: lazy_gname) (lvl: Z) : iProp Σ :=
      ∃ (S: gset node_rep), lazy_list head S Γ (Some γ) lvl.
    Definition skip_list (head: node_rep) (S: gset node_rep)
      (m: gmap Z (tval * list tval)) (mΓ: gmap Z lazy_gname) : iProp Σ :=
      jf_map head S m (mΓ !!! 0)
      ∗
      [∗ set] i ∈ zrange 0 (MAX_HEIGHT + 1), 
        is_lazy_list head (mΓ !!! i) (mΓ !!! (i - 1)) i.

    (* Representation predicate for maps with version control *)
    Definition vc_map (p: loc) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) : iProp Σ :=
      ∃ (head: node_rep) (S: gset node_rep),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        skip_list head S m mΓ.

    (* Needed for [vc_map] to be timeless *)
    Global Instance vl_timeless vl p : Timeless (vertical_list vl p).
    Proof. revert p; induction vl; apply _. Qed.
    Global Instance locked_val_timeless i l : Timeless (locked_val i l).
    Proof. unfold locked_val; case_decide; apply _. Qed.
  End invariant.

  Section proofs.
    Context `{!heapGS Σ, !skipG Σ}.
    Local Open Scope Z.

    Lemma singleton_frag_in (h n s: node_rep) (S: gset node_rep) (Γ: lazy_gname) 
      (γ: option lazy_gname) (lvl: Z) :
      ⌜ n = s ⌝ ∨ own Γ.(auth_gname) (◯ {[n]}) -∗ 
      lazy_list h S Γ γ lvl -∗ 
      ⌜ n ∈ {[s]} ∪ S ⌝.
    Proof.
      iIntros "Hnode Hlazy".
      iDestruct "Hlazy" as "(Hauth & Hdisj & Htoks & Hnexts & Hlocks & Hsubs)".
      iDestruct "Hnode" as "[->|Hnode]"; first (iPureIntro; set_solver).
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      iPureIntro; set_solver.
    Qed.

    Lemma node_has_next (head pred: node_rep) (S: gset node_rep) (Γ: lazy_gname)
      (γ: option lazy_gname) (lvl: Z) :
      ⌜ pred = head ⌝ ∨ own Γ.(auth_gname) (◯ {[pred]}) -∗
      lazy_list head S Γ γ lvl -∗
        ∃ (s: loc) (succ: node_rep), 
          (node_next pred +ₗ lvl) ↦{#1 / 2} #s
          ∗
          s ↦□ rep_to_node succ
          ∗
          (⌜ succ = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[succ]}))
          ∗
          ⌜ set_map node_key S ## zrange (node_key pred) (node_key succ) ⌝
          ∗
          ((node_next pred +ₗ lvl) ↦{#1 / 2} #s -∗ lazy_list head S Γ γ lvl).
    Proof.
      iIntros "#Hpred Hlazy".
      iDestruct (singleton_frag_in with "Hpred Hlazy") as %Hpred.
      iDestruct "Hlazy" as "(Hauth & Hdisj & Htoks & Hnexts & Hlocks & Hsubs)".
      rewrite (big_sepS_delete (has_next lvl Γ) _ pred) //.
      iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (s succ) "(Hnext & #Hs & #Hsucc & Hkeys)".
      iDestruct (own_valid_2 with "Hdisj Hkeys") as %[Hdisj _]%ZRange_disj.

      iExists s, succ; iFrame "# ∗"; iSplit; first done. iIntros "Hnext". 
      iAssert (has_next lvl Γ pred) with "[Hnext Hkeys]" as "Hnext".
      { iExists s, succ; iFrame "# ∗". }
      iCombine "Hnext Hnexts" as "Hnexts"; rewrite -big_sepS_delete //.
    Qed.

    Lemma node_has_lock (head node: node_rep) (S: gset node_rep) (Γ: lazy_gname)
      (γ: option lazy_gname) (lvl: Z) :
      ⌜ node = head ⌝ ∨ own Γ.(auth_gname) (◯ {[node]}) -∗
      lazy_list head S Γ γ lvl -∗
        has_lock lvl node ∗ (has_lock lvl node -∗ lazy_list head S Γ γ lvl).
    Proof.
      iIntros "#Hnode Hlazy".
      iDestruct (singleton_frag_in with "Hnode Hlazy") as %Hnode.
      iDestruct "Hlazy" as "(Hauth & Hdisj & Htoks & Hnexts & Hlocks & Hsubs)".
      rewrite (big_sepS_delete (has_lock lvl) _ node) //.
      iDestruct "Hlocks" as "(Hlock & Hlocks)".
      iFrame; iIntros "Hlock".
      iCombine "Hlock Hlocks" as "Hlocks"; rewrite -big_sepS_delete //.
    Qed.

    Definition opt_sub (mΓ: gmap Z lazy_gname) (lvl: Z) : option lazy_gname :=
      if decide (lvl = 0) then None
      else Some (mΓ !!! (lvl - 1)).
    Lemma skip_has_lazy (lvl: Z) (head: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      skip_list head S m mΓ ⊢
        ∃ (S': gset node_rep),
          lazy_list head S' (mΓ !!! lvl) (opt_sub mΓ lvl) lvl
          ∗ (
            lazy_list head S' (mΓ !!! lvl) (opt_sub mΓ lvl) lvl 
            -∗ 
            skip_list head S m mΓ
          )
          ∗
          ⌜ lvl = 0 → dom m = set_map node_key S' ⌝.
    Proof.
      iIntros "%Hlvl [[Hbot Hmap] Hskip]".
      destruct (Z.to_nat lvl) as [|lvl'] eqn:Heq.
      + replace lvl with 0 by lia. iExists S.
        iDestruct "Hmap" as (γ) "(%Hdom & Hauth & Hvals)".
        iFrame "Hbot". iSplit; last by iPureIntro.
        iIntros. iFrame. iExists γ. by iFrame.
      + rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
        iDestruct "Hskip" as "[[%S' Hlazy] Hskip]".
        iExists S'. unfold opt_sub; case_decide; first lia.
        iFrame. iSplit; last by iPureIntro. iIntros "Hlazy".
        iApply (big_sepS_delete _ _ lvl); first (rewrite zrange_spec; lia).
        iFrame. by iExists S'.
    Qed.

    Lemma node_in_lower (lvl: Z) (h n: node_rep)
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      1 ≤ lvl ≤ MAX_HEIGHT → 
      skip_list h S m mΓ -∗
      own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      own (mΓ !!! (lvl - 1)).(auth_gname) (◯ {[n]}).
    Proof.
      iIntros (Hlvl) "[[Hbot Hmap] Hskip] #Hnode".
      rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
      iDestruct "Hskip" as "[[%S' Hlazy] Hskip]".
      iDestruct "Hlazy" as "(Hauth & Hdisj & Htoks & Hnexts & Hlocks & Hsubs)".
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      rewrite (big_sepS_delete (has_sub _) _ n); last set_solver.
      by iDestruct "Hsubs" as "[[#Hfrag Htok] Hsubs]".
    Qed.

    Lemma sent_or_node_in_lower (lvl: Z) (h n s: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      1 ≤ lvl ≤ MAX_HEIGHT → 
      skip_list h S m mΓ -∗
      ⌜ n = s ⌝ ∨ own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      ⌜ n = s ⌝ ∨ own (mΓ !!! (lvl - 1)).(auth_gname) (◯ {[n]}).
    Proof.
      iIntros (Hlvl) "Hskip #Hnode".
      iDestruct "Hnode" as "[->|Hnode]"; first by iLeft. iRight.
      by iApply (node_in_lower with "Hskip Hnode").
    Qed.

    Lemma node_in_bot (lvl: Z) (h n: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      skip_list h S m mΓ -∗
      own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      own (mΓ !!! 0).(auth_gname) (◯ {[n]}).
    Proof.
      iIntros (Hlvl) "Hskip #Hnode".
      assert (lvl = Z.of_nat (Z.to_nat lvl)) as Heq by lia.
      iRevert (Hlvl); rewrite Heq; clear Heq.
      iInduction (Z.to_nat lvl) as [|lvl'] "Himp"; first by iIntros.
      iIntros "%Hlvl'".
      iDestruct (node_in_lower with "Hskip Hnode") as "#Hnode'"; first lia.
      replace (Datatypes.S lvl' - 1) with (Z.of_nat lvl') by lia.
      iApply ("Himp" with "Hnode' Hskip"). iPureIntro; lia.
    Qed.

    Lemma node_has_val (lvl: Z) (h n: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      skip_list h S m mΓ -∗
      own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      ∃ (val: val_rep) (vl: list tval),
        node_val n ↦{#1 / 2} rep_to_val val
        ∗
        ⌜ m !! node_key n = Some (val_vt val, vl) ⌝
        ∗
        (node_val n ↦{#1 / 2} rep_to_val val -∗ skip_list h S m mΓ).
    Proof.
      iIntros "%Hlvl Hskip #Hnode".
      iDestruct (node_in_bot with "Hskip Hnode") as "#Hnode'"; first done.
      iDestruct "Hskip" as "[[Hlazy Hmap] Hskip]".
      iDestruct "Hlazy" as "(Hauth & Hdisj & Htoks & Hnexts & Hlocks & Hsubs)".
      iDestruct (own_valid_2 with "Hauth Hnode'") 
        as %[?%gset_included]%auth_both_valid_discrete.

      iDestruct "Hmap" as (γ) "(Hdom & Hgmap & Hvals)".
      rewrite (big_sepS_delete (has_val _) _ n); last set_solver.
      iDestruct "Hvals" as "[Hval Hvals]".
      iDestruct "Hval" as (val vl) "(Hpt & Hvt & Hvl)".
      iDestruct (ghost_map_lookup with "Hgmap Hvt") as %Hsome.

      iExists val, vl. iFrame "Hpt". iSplit; first done.
      iIntros "Hpt". iFrame. iExists γ. iFrame "Hgmap".
      iApply (big_sepS_delete _ _ n); first set_solver.
      iFrame "Hvals". iExists val, vl. iFrame.
    Qed.

    Lemma map_has_skip (p: loc) (head: node_rep) (m: gmap Z (tval * list tval)) 
      (mΓ: gmap Z lazy_gname) :
      p ↦□ rep_to_node head -∗
      vc_map p m mΓ -∗
        ∃ (S : gset node_rep), 
          (skip_list head S m mΓ)
          ∗ 
          (skip_list head S m mΓ -∗ vc_map p m mΓ).
    Proof.
      iIntros "Hhead Hmap". iDestruct "Hmap" as (h' S) "(#H & %Hmin & Hskip)".
      iDestruct (mapsto_agree with "Hhead H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame "Hskip". iIntros "Hskip". iExists head, S. by iFrame.
    Qed. 
  End proofs.
End SkipListInv.