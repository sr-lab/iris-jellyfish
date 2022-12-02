From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.skip_list.lists Require Import code.
From SkipList.lib Require Import misc node_rep node_lt.
From SkipList.skip_list.lists.inv Require Import list_equiv.


Class skipGS Σ := SkipGS { 
  frac_gsetR :> inG Σ (frac_authR (gsetUR Z));
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

Local Open Scope Z.

Module LazyListInv (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module ListEquiv := ListEquiv Params.
  Export ListEquiv.

  Section Proofs.
    Context `{!heapGS Σ, !skipGS Σ, !lockG Σ} (N: namespace).

    Definition is_node (obot: option sub_gname) (key: Z) (odown: option loc) : iProp Σ := 
      match obot, odown with
      | Some bot, Some d => ∃ (down: node_rep),
                            d ↦ rep_to_node down
                            ∗
                            own (s_auth bot) (◯ {[ down ]})
                            ∗
                            own (s_toks bot) (◯ GSet {[ node_key down ]})
                            ∗
                            ⌜ key = node_key down ⌝
      | None, None => True
      | _, _ => False
      end.

    Definition sub_list_inv (head: node_rep) (Γ: sub_gname) (osub: option sub_gname)
      (S: gset node_rep) (L: list node_rep) : iProp Σ := 
      ⌜ Permutation L (elements S) ⌝
      ∗
      ⌜ Sorted node_lt ([head] ++ L ++ [tail]) ⌝
      ∗
      own (s_auth Γ) (● S)
      ∗
      own (s_toks Γ) (● GSet (set_map node_key S))
      ∗
      list_equiv ([head] ++ L) (is_node osub).
    
    Definition lazy_list_inv (head: node_rep) (obot: option bot_gname) 
      (Γ: sub_gname) (osub: option sub_gname) : iProp Σ := 
      ∃ (S: gset node_rep) (L: list node_rep),
        sub_list_inv head Γ osub S L
        ∗
        match obot with
        | Some bot => own (s_frac bot) (●F (set_map node_key S))
        | None => True
        end.

    Definition is_sub_list (head: node_rep) (Γ γ: sub_gname) : iProp Σ := 
      inv N (lazy_list_inv head None Γ (Some γ)).

    Definition is_bot_list (head: node_rep) (Skeys: gset Z) (q: frac)
      (bot: bot_gname) (Γ: sub_gname) : iProp Σ := 
      own (s_frac bot) (◯F{q} Skeys)
      ∗
      inv N (lazy_list_inv head (Some bot) Γ None).

  End Proofs.
End LazyListInv.