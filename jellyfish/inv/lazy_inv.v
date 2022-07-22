From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import cmra auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt key_equiv.
From SkipList.jellyfish Require Import list_equiv.

Module LazyListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ} (lvl: Z).

    Definition node_key_range : gset Z := Zlt_range INT_MIN INT_MAX.

    Definition sub_list_inv (head: node_rep) (Γ: sub_gname) 
      (osub: option sub_gname) (omap: option (gmap Z (argmax Z)))
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
      list_equiv lvl osub ([head] ++ L) omap.

    Definition bot_list_inv (Γ: bot_gname) (Smap: gmap Z (argmax Z)) : iProp Σ := 
      own (s_frac Γ) (●F Smap)
      ∗
      own (s_keys Γ) (GSet (node_key_range ∖ (dom Smap))).

    Definition lazy_list_inv (head: node_rep) (bot: bot_gname)
      (top_sub: sub_gname) (obot_sub: option sub_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (Smap: gmap Z (argmax Z)) (L: list node_rep),
        sub_list_inv head top_sub obot_sub (opt_map obot_sub Smap) S (dom Smap) L
        ∗
        match obot_sub with
        | Some bot_sub => True
        | None => bot_list_inv bot Smap
        end.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Definition is_sub_list (head: node_rep) (bot: bot_gname) (top_sub bot_sub: sub_gname) : iProp Σ := 
      inv (levelN lvl) (lazy_list_inv head bot top_sub (Some bot_sub)).

    Definition is_bot_list (head: node_rep) (Smap: gmap Z (argmax Z)) (q: frac)
      (bot: bot_gname) (sub: sub_gname) : iProp Σ := 
      own (s_frac bot) (◯F{q} Smap)
      ∗
      inv (levelN lvl) (lazy_list_inv head bot sub None).

  End Proofs.
End LazyListInv.