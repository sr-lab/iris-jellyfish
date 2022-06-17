From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list Require Import node_lt node_rep code key_equiv.
From SkipList.skip_list.inv Require Import list_equiv.


Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_nr_F_inGS :> inG Σ (frac_authR (gsetUR node_rep));
  gset_Z_disj_inGS :> inG Σ (gset_disjUR Z)
}.

Local Open Scope Z.
Module LazyListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Record sub_gname := mk_sub_gname {
    s_auth: gname;
    s_toks: gname
  }.

  Record bot_gname := mk_bot_gname {
    s_frac: gname;
    s_keys: gname
  }.

  Section Proofs.
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (N: namespace).

    Definition from_sub_list (obot: option sub_gname) (key: Z) (odown: option loc) : iProp Σ := 
      match obot, odown with
      | None, None => True
      | Some bot, Some d => ∃ (down: node_rep),
                            d ↦ rep_to_node down
                            ∗
                            own (s_auth bot) (◯ {[ down ]})
                            ∗
                            own (s_toks bot) (GSet {[ node_key down ]})
                            ∗
                            ⌜ key = node_key down ⌝
      | _, _ => False
      end.

    Definition from_bot_list : Z → option loc → iProp Σ := 
      from_sub_list None.

    Definition from_top_list (bot: sub_gname) : Z → option loc → iProp Σ := 
      from_sub_list (Some bot).

    Definition node_key_range : gset Z := Zlt_range INT_MIN INT_MAX.

    Definition sub_list_inv (head: node_rep) (Γ: sub_gname) (P: Z → option loc → iProp Σ) 
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
      list_equiv ([head] ++ L) P.

    Definition bot_list_inv (Γ: bot_gname) (S: gset node_rep) (Skeys: gset Z) : iProp Σ := 
      own (s_frac Γ) (●F S)
      ∗
      own (s_keys Γ) (GSet (node_key_range ∖ Skeys)).
    
    Definition lazy_list_inv (head: node_rep) (P: Z → option loc → iProp Σ) 
      (sub: sub_gname) (obot: option bot_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (Skeys: gset Z) (L: list node_rep),
      sub_list_inv head sub P S Skeys L
      ∗
      match obot with
      | None => True
      | Some bot => bot_list_inv bot S Skeys
      end.

    Definition is_top_list (head: node_rep) (top bot: sub_gname) : iProp Σ := 
      inv N (lazy_list_inv head (from_top_list bot) top None).

    Definition is_bot_list (head: node_rep) (q: frac)
      (Skeys: gset Z) (sub: sub_gname) (bot: bot_gname) : iProp Σ := 
      ∃ (Sfrac: gset node_rep),
      ⌜ key_equiv Sfrac Skeys ⌝
      ∗
      own (s_frac bot) (◯F{q} Sfrac)
      ∗
      inv N (lazy_list_inv head from_bot_list sub (Some bot)).

  End Proofs.
End LazyListInv.