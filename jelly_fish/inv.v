From iris.algebra Require Import gmap gset excl_auth dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import zrange gmap_extra.
From SkipList.jelly_fish Require Import code.


Class skipG Σ := SkipG { 
  skip_authG :> inG Σ (authR (gsetR node_rep));
  skip_disjG :> inG Σ (gset_disjR Z);
  skip_toksG :> inG Σ (authR (gset_disjR Z));
  skip_exclG :> inG Σ (excl_authR (gset Z));
  skip_valsG :> inG Σ (authR (gmap_disjR Z (Z * Z)));
  skip_lockG :> lockG Σ
}.

Record inv_gname := mk_inv_gname {
  auth_gname: gname;
  disj_gname: gname;
  toks_gname: gname
}.
Global Instance inv_gname_inhabited : Inhabited inv_gname := 
  populate (mk_inv_gname inhabitant inhabitant inhabitant).

Record map_gname := mk_map_gname {
  excl_gname: gname;
  vals_gname: gname
}.

Module SkipListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module SkipList := SkipList Params.
  Export SkipList.

  Section invariant.
    Context `{!heapGS Σ, !skipG Σ} (N: namespace).
    Local Open Scope Z.

    Definition locked_val (lvl: Z) (n: loc) : iProp Σ := 
      if decide (lvl = 0) then 
        (∃ (node: node_rep), n ↦□ rep_to_node node ∗
        (⌜ node = tail ⌝ ∨ ∃ (val: val_rep), (node_val node) ↦{#1 / 2} rep_to_val val))%I
      else True%I.
    Definition in_lock (lvl: Z) (a: loc) : iProp Σ := 
      ∃ (n: loc), (a +ₗ lvl) ↦{#1 / 2} #n ∗ locked_val lvl n.
    Definition has_lock (lvl: Z) (node: node_rep) : iProp Σ := 
      ∃ (γl: gname) (l: val), 
        (node_lock node +ₗ lvl) ↦□ l
        ∗
        is_lock γl l (in_lock lvl (node_next node)).

    Definition has_next (lvl: Z) (Γi: inv_gname) (pred: node_rep) : iProp Σ :=
      ∃ (s: loc) (succ: node_rep), 
        (node_next pred +ₗ lvl) ↦{#1 / 2} #s
        ∗
        s ↦□ rep_to_node succ
        ∗
        (⌜ succ = tail ⌝ ∨ own Γi.(auth_gname) (◯ {[succ]}))
        ∗
        own Γi.(disj_gname) (ZRange (node_key pred) (node_key succ)).

    Definition has_val (Γm: map_gname) (node: node_rep) : iProp Σ :=
      ∃ (val: val_rep),
        (node_val node) ↦{#1 / 2} rep_to_val val
        ∗
        own Γm.(vals_gname) (◯ DMap {[ node_key node := (val_vt val)]}).
    Definition own_map (S: gset node_rep) (Γm: map_gname) : iProp Σ :=
      own Γm.(excl_gname) (●E (set_map node_key S))
      ∗
      [∗ set] n ∈ S, has_val Γm n.

    Definition has_frag (γi: inv_gname) (node: node_rep) : iProp Σ :=
      own γi.(auth_gname) (◯ {[ node ]})
      ∗
      own γi.(toks_gname) (◯ GSet {[ node_key node ]}).

    Definition lazy_list_inv (head: node_rep) (Γm: map_gname) (Γ: gmap Z inv_gname) (lvl: Z) : iProp Σ :=
      ∃ (S: gset node_rep),
        own (Γ !!! lvl).(auth_gname) (● S)
        ∗
        own (Γ !!! lvl).(disj_gname) (GSet (set_map node_key S))
        ∗
        own (Γ !!! lvl).(toks_gname) (● GSet (set_map node_key S))
        ∗
        ([∗ set] n ∈ {[head]} ∪ S, has_lock lvl n)
        ∗
        ([∗ set] n ∈ {[head]} ∪ S, has_next lvl (Γ !!! lvl) n)
        ∗
        if decide (lvl = 0) then own_map S Γm
        else [∗ set] n ∈ S, has_frag (Γ !!! (lvl - 1)) n.
    Definition skip_list_inv (head: node_rep) (Γm: map_gname) (Γ: gmap Z inv_gname) : iProp Σ :=
      [∗ set] i ∈ zrange (-1) (MAX_HEIGHT + 1), lazy_list_inv head Γm Γ i.

    Definition skipN := N .@ "skip".
    Definition map_inv (p: loc) (Γm: map_gname) : iProp Σ :=
      ∃ (head: node_rep) (Γ: gmap Z inv_gname),
        p ↦□ rep_to_node head
        ∗
        ⌜ node_key head = INT_MIN ⌝
        ∗
        inv skipN (skip_list_inv head Γm Γ).

    Definition map (m: gmap Z (Z * Z)) (Γm: map_gname) : iProp Σ := 
      own Γm.(excl_gname) (◯E (dom m))
      ∗
      own Γm.(vals_gname) (● DMap m).

  End invariant.

  Section proofs.
    Context `{!heapGS Σ, !skipG Σ} (N: namespace).
    Local Open Scope Z.

    Lemma singleton_frag_in (S: gset node_rep) (n s: node_rep) (γ: gname) :
      own γ (● S) -∗ ⌜ n = s ⌝ ∨ own γ (◯ {[n]}) → ⌜ n ∈ {[s]} ∪ S ⌝.
    Proof.
      iIntros "Hauth Hnode".
      iDestruct "Hnode" as "[->|Hnode]"; first (iPureIntro; set_solver).
      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      iPureIntro; set_solver.
    Qed.

    Lemma has_lvl_inv (lvl: Z) (head: node_rep) 
      (Γm: map_gname) (Γ: gmap Z inv_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      skip_list_inv head Γm Γ ⊢
        lazy_list_inv head Γm Γ lvl
        ∗
        (lazy_list_inv head Γm Γ lvl -∗ skip_list_inv head Γm Γ).
    Proof.
      intros Hlvl; unfold skip_list_inv.
      rewrite (big_sepS_delete _ _ lvl); last (rewrite zrange_spec; lia).
      iIntros "(Hlvl & Hskip)"; iFrame; by iIntros.
    Qed.

    Lemma frag_has_val (lvl: Z) (head node: node_rep) 
      (Γm: map_gname) (Γ: gmap Z inv_gname) :
      0 ≤ lvl ≤ MAX_HEIGHT →
      skip_list_inv head Γm Γ -∗
      own (Γ !!! lvl).(auth_gname) (◯ {[node]}) -∗
          has_val Γm node
          ∗
          (has_val Γm node -∗ skip_list_inv head Γm Γ).
    Proof.
      iIntros (Hlvl) "Hskip Hnode".
      assert (lvl = Z.of_nat (Z.to_nat lvl)) as Heq by lia.
      iRevert (Hlvl) "Hnode"; rewrite Heq; clear Heq.
      iInduction (Z.to_nat lvl) as [|lvl'] "Himp"; iIntros "%Hlvl Hnode".
      + iDestruct (has_lvl_inv 0 with "Hskip") as "(Hlvl & Hskip)"; first (pose HMAX_HEIGHT; lia).
        iDestruct "Hlvl" as (S) "(Hauth & ? & ? & ? & ? & Hmap)".
        iDestruct (own_valid_2 with "Hauth Hnode") as %[?%gset_included]%auth_both_valid_discrete.
        iDestruct "Hmap" as "(Hexcl● & Hvals◯)".
        rewrite (big_sepS_delete (has_val _) _ node); last set_solver.
        iDestruct "Hvals◯" as "(Hval & Hvals◯)"; iFrame.
        iIntros "Hval"; iCombine "Hval Hvals◯" as "Hvals◯". 
        rewrite -big_sepS_delete; last set_solver.
        iApply "Hskip"; iExists S; iFrame.
      + iDestruct (has_lvl_inv with "Hskip") as "(Hlvl & Hskip)"; first done.
        iDestruct "Hlvl" as (S) "(Hauth & ? & ? & ? & ? & Hfrags)".
        case_decide; first lia.
        iDestruct (own_valid_2 with "Hauth Hnode") as %[?%gset_included]%auth_both_valid_discrete.
        rewrite (big_sepS_delete (has_frag _) _ node); last set_solver.
        iDestruct "Hfrags" as "((#Hnode' & ?) & Hfrags)".
        iAssert (has_frag _ _) with "[$]" as "Hfrag".
        iCombine "Hfrag Hfrags" as "Hfrags".
        rewrite -(big_sepS_delete (has_frag _)); last set_solver.
        replace (Z.of_nat lvl') with (Datatypes.S lvl' - 1) by lia.
        iApply ("Himp" with "[-] [%] [$]"); last lia.
        iApply "Hskip". iExists S; case_decide; first lia; iFrame.
    Qed.

    Lemma has_lower_frag (lvl: Z) (head node: node_rep) 
      (Γm: map_gname) (Γ: gmap Z inv_gname) :
      0 < lvl ≤ MAX_HEIGHT →
      inv (skipN N) (skip_list_inv head Γm Γ) -∗
      ⌜ node = head ⌝ ∨ own (auth_gname (Γ !!! lvl)) (◯ {[node]}) ={⊤}=∗
      ⌜ node = head ⌝ ∨ own (auth_gname (Γ !!! (lvl - 1))) (◯ {[node]}).
    Proof.
      iIntros (Hlvl) "#Hinv Hnode".
      iDestruct "Hnode" as "[->|Hnode]"; first by (iModIntro; iLeft).
      iInv "Hinv" as "Hskip".
      iDestruct (has_lvl_inv lvl with "Hskip") as "(Hlvl & Hskip)"; first lia.
      iDestruct "Hlvl" as (S) "(>Hauth & ? & ? & ? & ? & Hfrags)".
      case_decide; first lia; iMod "Hfrags".

      iDestruct (own_valid_2 with "Hauth Hnode") 
        as %[?%gset_included]%auth_both_valid_discrete.
      rewrite (big_sepS_delete (has_frag _) _ node); last set_solver.
      iDestruct "Hfrags" as "((#Hnode' & ?) & Hfrags)".
      iAssert (has_frag _ _) with "[$]" as "Hfrag".
      iCombine "Hfrag Hfrags" as "Hfrags".
      rewrite -(big_sepS_delete (has_frag _)); last set_solver.

      iModIntro; iSplitR ""; last (iModIntro; iFrame "Hnode'").
      iNext; iApply "Hskip"; iExists S; case_decide; first lia; iFrame.
    Qed.
  End proofs.
End SkipListInv.