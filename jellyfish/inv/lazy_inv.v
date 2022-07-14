From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import cmra auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish Require Import list_equiv.

Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (frac_authR (gmapUR Z (arg_maxR Z)));
  gset_nr_F_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_Z_disj_inGS :> inG Σ (gset_disjR Z)
}.

Record sub_gname := mk_sub_gname {
  s_auth: gname;
  s_toks: gname
}.

Record bot_gname := mk_bot_gname {
  s_frac: gname
}.

Module LazyListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvl: Z).

    Definition from_sub_list (sub: sub_gname) (rep: node_rep) : iProp Σ := 
      own (s_auth sub) (◯ {[ rep ]})
      ∗
      own (s_toks sub) (GSet {[ node_key rep ]}).

    Definition from_bot_list (Smap: gmap Z (prodZ Z)) (rep: node_rep) : iProp Σ := 
      ∃ (v: val_rep) (vs: gset Z), 
        (node_val rep) ↦{#1 / 2} rep_to_val v
        ∗
        ⌜ Smap !! (node_key rep) = Some (vs, val_ts v) ⌝
        ∗
        ⌜ val_v v ∈ vs ⌝.

    Definition node_key_range : gset Z := Zlt_range INT_MIN INT_MAX.

    Definition sub_list_inv (head: node_rep) (Γ: sub_gname) (P: node_rep → iProp Σ) 
      (S: gset node_rep) (Skeys: gset Z) (L: list node_rep) : iProp Σ := 
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      ⌜ key_equiv S Skeys ⌝
      ∗
      own (s_auth Γ) (● S)
      ∗
      own (s_toks Γ) (GSet (node_key_range ∖ Skeys))
      ∗
      list_equiv lvl ([head] ++ L) P.

    Definition lazy_list_inv (head: node_rep) (bot: bot_gname)
      (top_sub: sub_gname) (obot_sub: option sub_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (Smap: gmap Z (prodZ Z)) (L: list node_rep),
      match obot_sub with
      | Some bot_sub => sub_list_inv head top_sub (from_sub_list bot_sub) S (dom Smap) L
      | None => sub_list_inv head top_sub (from_bot_list Smap) S (dom Smap) L
                ∗
                own (s_frac bot) (●F Smap)
      end.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Definition is_sub_list (head: node_rep) (bot: bot_gname) (top_sub bot_sub: sub_gname) : iProp Σ := 
      inv (levelN lvl) (lazy_list_inv head bot top_sub (Some bot_sub)).

    Definition is_bot_list (head: node_rep) (Smap: gmap Z (prodZ Z)) (q: frac)
      (bot: bot_gname) (sub: sub_gname) : iProp Σ := 
      own (s_frac bot) (◯F{q} Smap)
      ∗
      inv (levelN lvl) (lazy_list_inv head bot sub None).

    
    Lemma lazy_match_inv (head: node_rep) (bot: bot_gname)
      (sub: sub_gname) (obot: option sub_gname) :
      lazy_list_inv head bot sub obot ⊢
        ∃ (P: node_rep → iProp Σ) (S: gset node_rep) (Skeys: gset Z) (L: list node_rep),
          sub_list_inv head sub P S Skeys L
          ∗
          (sub_list_inv head sub P S Skeys L -∗ lazy_list_inv head bot sub obot).
    Proof.
      destruct obot as [bot_sub|].
      + iIntros "Hsub"; unfold lazy_list_inv.
        iDestruct "Hsub" as (S Smap L) "Hsub".
        iExists (from_sub_list bot_sub), S, (dom Smap), L.
        iFrame. iIntros "Hsub".
        iExists S, Smap, L; iFrame.
      + iIntros "Hbot"; unfold lazy_list_inv.
        iDestruct "Hbot" as (S Smap L) "(Hsub & Hown)".
        iExists (from_bot_list Smap), S, (dom Smap), L.
        iFrame. iIntros "Hsub".
        iExists S, Smap, L; iFrame.
    Qed.

  End Proofs.
End LazyListInv.