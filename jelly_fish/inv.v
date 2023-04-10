From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.heap_lang Require Import notation.
Import derived_laws_later.bi.

From SkipList.lib Require Import zrange.
From SkipList.atomic Require Import proofmode lock.
From SkipList.jelly_fish Require Import code.


Definition tval : Type := Z * Z.

Class skipG Σ := SkipG { 
  skip_authG :: inG Σ (authR (gset node_rep));
  skip_sortG :: inG Σ (gset_disjR Z);
  skip_toksG :: inG Σ (authR (gset_disjR Z));
  skip_gmapG :: ghost_mapG Σ Z (tval * list tval)
}.

Record lazy_gname := mk_lazy_gname {
  auth_gname: gname;
  sort_gname: gname;
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
    Definition has_next (lvl: Z) (Γ: lazy_gname) (n: node_rep) : iProp Σ :=
      ∃ (p: loc) (s: node_rep), 
        (node_next n +ₗ lvl) ↦{#1 / 2} #p
        ∗
        p ↦□ rep_to_node s
        ∗
        (⌜ s = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[s]}))
        ∗
        own Γ.(sort_gname) (ZRange (node_key n) (node_key s)).

    (* Lock resources *)
    Definition locked_val (lvl: Z) (p: loc) : iProp Σ := 
      if lvl is 0 then 
        (∃ (s: node_rep), p ↦□ rep_to_node s ∗
        (⌜ s = tail ⌝ ∨ ∃ (v: val_rep), node_val s ↦{#1 / 2} rep_to_val v))%I
      else emp%I.
    Definition in_lock (lvl: Z) (n: node_rep) : iProp Σ := 
      ∃ (p: loc), (node_next n +ₗ lvl) ↦{#1 / 2} #p ∗ locked_val lvl p.
    Definition has_lock (lvl: Z) (n: node_rep) : iProp Σ := 
      ∃ (st: state), lock #(node_lock n +ₗ lvl) st ∗
        match st with Free => in_lock lvl n | Locked => emp end.

    (* Sublist resources *)
    Definition has_sub (γ: lazy_gname) (n: node_rep) : iProp Σ :=
      own γ.(auth_gname) (◯ {[ n ]})
      ∗
      own γ.(toks_gname) (◯ GSet {[ node_key n ]}).

    (* Lazy list resources for a given level *)
    Definition lazy_list (h: node_rep) (S: gset node_rep)
      (Γ: lazy_gname) (γ: option lazy_gname) (lvl: Z) : iProp Σ :=
      own Γ.(auth_gname) (● S)
      ∗
      own Γ.(toks_gname) (● GSet (set_map node_key S))
      ∗
      own Γ.(sort_gname) (GSet (set_map node_key S))
      ∗
      ([∗ set] n ∈ {[h]} ∪ S, has_next lvl Γ n)
      ∗
      ([∗ set] n ∈ {[h]} ∪ S, has_lock lvl n)
      ∗
      match γ with None => emp | Some γ => [∗ set] n ∈ S, has_sub γ n end.

    (* Vertical list resources *)
    Fixpoint vertical_list (p: loc) (vl: list tval) : iProp Σ := 
      match vl with
      | nil => ⌜ p = dummy_null ⌝
      | vt :: vl => ∃ (n: loc), p ↦□ rep_to_val (vt, n)%core ∗ vertical_list n vl
      end.
    Definition has_val (γ: gname) (n: node_rep) : iProp Σ :=
      ∃ (v: val_rep) (vl: list tval),
        node_val n ↦{#1 / 2} rep_to_val v
        ∗
        node_key n ↪[γ] (val_vt v, vl)
        ∗
        vertical_list (val_p v) vl.

    (* JellyFish map resources *)
    Definition jf_map (h: node_rep) (S: gset node_rep) 
      (m: gmap Z (tval * list tval)) (Γ: lazy_gname) : iProp Σ :=
      lazy_list h S Γ None 0
      ∗
      ∃ (γ: gname),
        ⌜ dom m = set_map node_key S ⌝
        ∗
        ghost_map_auth γ 1 m
        ∗
        [∗ set] n ∈ S, has_val γ n.

    (* Skip list resources *)
    Definition is_lazy_list (h: node_rep) (Γ: lazy_gname)
      (γ: lazy_gname) (lvl: Z) : iProp Σ :=
      ∃ (S: gset node_rep), lazy_list h S Γ (Some γ) lvl.
    Definition jelly_fish (h: node_rep) (S: gset node_rep)
      (m: gmap Z (tval * list tval)) (mΓ: gmap Z lazy_gname) : iProp Σ :=
      jf_map h S m (mΓ !!! 0)
      ∗
      [∗ set] i ∈ zrange 0 (MAX_HEIGHT + 1), 
        is_lazy_list h (mΓ !!! i) (mΓ !!! (i - 1)) i.

    (* Representation predicate for maps with version control *)
    Definition vc_map (p: loc) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) : iProp Σ :=
      ∃ (h: node_rep) (S: gset node_rep),
        p ↦□ rep_to_node h
        ∗
        ⌜ node_key h = INT_MIN ⌝
        ∗
        jelly_fish h S m mΓ.

    Global Instance vl_timeless vl p : Timeless (vertical_list p vl).
    Proof. revert p; induction vl; apply _. Qed.
    Global Instance locked_val_timeless i l : Timeless (locked_val i l).
    Proof. unfold locked_val; case_match; apply _. Qed.
    Global Instance has_lock_timeless i n : Timeless (has_lock i n).
    Proof. apply bi.exist_timeless; intros; case_match; apply _. Qed.
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
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".
      iDestruct "Hnode" as "[->|Hnode]"; first (iPureIntro; set_solver).
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      iPureIntro; set_solver.
    Qed.

    Lemma node_has_next (h n: node_rep) (S: gset node_rep) (Γ: lazy_gname)
      (γ: option lazy_gname) (lvl: Z) :
      ⌜ n = h ⌝ ∨ own Γ.(auth_gname) (◯ {[n]}) -∗
      lazy_list h S Γ γ lvl -∗
        ∃ (p: loc) (s: node_rep), 
          (node_next n +ₗ lvl) ↦{#1 / 2} #p
          ∗
          p ↦□ rep_to_node s
          ∗
          (⌜ s = tail ⌝ ∨ own Γ.(auth_gname) (◯ {[s]}))
          ∗
          ⌜ set_map node_key S ## zrange (node_key n) (node_key s) ⌝
          ∗
          ((node_next n +ₗ lvl) ↦{#1 / 2} #p -∗ lazy_list h S Γ γ lvl).
    Proof.
      iIntros "#Hn Hlazy".
      iDestruct (singleton_frag_in with "Hn Hlazy") as %Hn.
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".
      rewrite (big_sepS_delete (has_next lvl Γ) _ n) //.
      iDestruct "Hnexts" as "(Hnext & Hnexts)".
      iDestruct "Hnext" as (p s) "(Hnext & #Hp & #Hs & Hkeys)".
      iDestruct (own_valid_2 with "Hsort Hkeys") as %[Hdisj _]%ZRange_disj.

      iExists p, s; iFrame "# ∗"; iSplit; first done. iIntros "Hnext". 
      iAssert (has_next lvl Γ n) with "[Hnext Hkeys]" as "Hnext".
      { iExists p, s; iFrame "# ∗". }
      iCombine "Hnext Hnexts" as "Hnexts"; rewrite -big_sepS_delete //.
    Qed.

    Lemma node_has_lock (h n: node_rep) (S: gset node_rep) (Γ: lazy_gname)
      (γ: option lazy_gname) (lvl: Z) :
      ⌜ n = h ⌝ ∨ own Γ.(auth_gname) (◯ {[n]}) -∗
      lazy_list h S Γ γ lvl -∗
        has_lock lvl n ∗ (has_lock lvl n -∗ lazy_list h S Γ γ lvl).
    Proof.
      iIntros "#Hn Hlazy".
      iDestruct (singleton_frag_in with "Hn Hlazy") as %Hn.
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".
      rewrite (big_sepS_delete (has_lock lvl) _ n) //.
      iDestruct "Hlocks" as "(Hlock & Hlocks)".
      iFrame; iIntros "Hlock".
      iCombine "Hlock Hlocks" as "Hlocks"; rewrite -big_sepS_delete //.
    Qed.

    Definition opt_sub (mΓ: gmap Z lazy_gname) (lvl: Z) : option lazy_gname :=
      if decide (lvl = 0) then None
      else Some (mΓ !!! (lvl - 1)).
    Lemma skip_has_lazy (lvl: Z) (h: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      jelly_fish h S m mΓ ⊢
        ∃ (S': gset node_rep),
          lazy_list h S' (mΓ !!! lvl) (opt_sub mΓ lvl) lvl
          ∗ (
            lazy_list h S' (mΓ !!! lvl) (opt_sub mΓ lvl) lvl 
            -∗ 
            jelly_fish h S m mΓ
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
      jelly_fish h S m mΓ -∗
      own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      own (mΓ !!! (lvl - 1)).(auth_gname) (◯ {[n]}).
    Proof.
      iIntros (Hlvl) "[[Hbot Hmap] Hskip] #Hnode".
      rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
      iDestruct "Hskip" as "[[%S' Hlazy] Hskip]".
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      rewrite (big_sepS_delete (has_sub _) _ n); last set_solver.
      by iDestruct "Hsubs" as "[[#Hfrag Htok] Hsubs]".
    Qed.

    Lemma sent_or_node_in_lower (lvl: Z) (h n s: node_rep) 
      (S: gset node_rep) (m: gmap Z (tval * list tval))
      (mΓ: gmap Z lazy_gname) :
      1 ≤ lvl ≤ MAX_HEIGHT → 
      jelly_fish h S m mΓ -∗
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
      jelly_fish h S m mΓ -∗
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
      jelly_fish h S m mΓ -∗
      own (mΓ !!! lvl).(auth_gname) (◯ {[n]}) -∗
      ∃ (val: val_rep) (vl: list tval),
        node_val n ↦{#1 / 2} rep_to_val val
        ∗
        ⌜ m !! node_key n = Some (val_vt val, vl) ⌝
        ∗
        (node_val n ↦{#1 / 2} rep_to_val val -∗ jelly_fish h S m mΓ).
    Proof.
      iIntros "%Hlvl Hskip #Hnode".
      iDestruct (node_in_bot with "Hskip Hnode") as "#Hnode'"; first done.
      iDestruct "Hskip" as "[[Hlazy Hmap] Hskip]".
      iDestruct "Hlazy" as "(Hauth & Htoks & Hsort & Hnexts & Hlocks & Hsubs)".
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

    Lemma map_has_skip (p: loc) (h: node_rep) (m: gmap Z (tval * list tval)) 
      (mΓ: gmap Z lazy_gname) :
      p ↦□ rep_to_node h -∗
      vc_map p m mΓ -∗
        ∃ (S : gset node_rep), 
          (jelly_fish h S m mΓ)
          ∗ 
          (jelly_fish h S m mΓ -∗ vc_map p m mΓ).
    Proof.
      iIntros "Hh Hmap". iDestruct "Hmap" as (h' S) "(#H & %Hmin & Hskip)".
      iDestruct (mapsto_agree with "Hh H") as %<-%rep_to_node_inj; iClear "H".
      iExists S. iFrame "Hskip". iIntros "Hskip". iExists h, S. by iFrame.
    Qed. 
  End proofs.
End SkipListInv.