From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import cmra auth frac_auth gmap gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import arg_max.
From SkipList.jelly_fish Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.jelly_fish Require Import list_equiv.

Module LazyListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ} (lvl: Z).

    Definition opt_map (osub: option sub_gname) (M: gmap Z (argmax Z)) : option (gmap Z (argmax Z)) :=
      match osub with
      | Some _ => None
      | None => Some M
      end.

    Definition sub_list_inv (head: node_rep) (Γ: sub_gname) (osub: option sub_gname) 
      (M: gmap Z (argmax Z)) (S: gset node_rep) (L: list node_rep) : iProp Σ := 
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      own (s_auth Γ) (● S)
      ∗
      own (s_toks Γ) (● GSet (set_map node_key S))
      ∗
      list_equiv lvl osub ([head] ++ L) (opt_map osub M).

    Definition lazy_list_inv (head: node_rep) (obot: option bot_gname)
      (Γ: sub_gname) (osub: option sub_gname) : iProp Σ := 
        ∃ (M: gmap Z (argmax Z)) (S: gset node_rep) (L: list node_rep),
          sub_list_inv head Γ osub M S L
          ∗
          match obot with
          | Some bot => own (s_frac bot) (●F M) ∗ ⌜ dom M = set_map node_key S ⌝
          | None => True
          end.

    Definition levelN (lvl: Z) := nroot .@ "level" .@ lvl.

    Definition is_sub_list (head: node_rep) (Γ γ: sub_gname) : iProp Σ := 
      inv (levelN lvl) (lazy_list_inv head None Γ (Some γ)).

    Definition is_bot_list (head: node_rep) (M: gmap Z (argmax Z)) (q: frac)
      (bot: bot_gname) (Γ: sub_gname) : iProp Σ := 
      own (s_frac bot) (◯F{q} M)
      ∗
      inv (levelN lvl) (lazy_list_inv head (Some bot) Γ None).

  End Proofs.
End LazyListInv.