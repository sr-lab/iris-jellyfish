From Coq Require Import Sorting.Sorted.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth frac_auth gset.
From iris.heap_lang Require Import proofmode.

From SkipList.lib Require Import lock misc node_rep node_lt key_equiv.
From SkipList.arrays Require Import code.
From SkipList.arrays.inv Require Import list_equiv.


Class gset_list_unionGS Σ := GsetGS { 
  gset_nr_A_inGS :> inG Σ (authR (gsetUR node_rep));
  gset_nr_F_inGS :> inG Σ (frac_authR (gsetUR Z));
  gset_Z_disj_inGS :> inG Σ (gset_disjUR Z)
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
    Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ} (lvl: nat).

    Definition from_sub_list (obot: option sub_gname) (rep: node_rep) : iProp Σ := 
      match obot with
      | None => True
      | Some bot => own (s_auth bot) (◯ {[ rep ]})
                    ∗
                    own (s_toks bot) (GSet {[ node_key rep ]})
      end.

    Definition from_bot_list : node_rep → iProp Σ := 
      from_sub_list None.

    Definition from_top_list (bot: sub_gname) : node_rep → iProp Σ := 
      from_sub_list (Some bot).

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

    Definition bot_list_inv (Γ: bot_gname) (Skeys: gset Z) : iProp Σ := 
      own (s_frac Γ) (●F Skeys).
    
    Definition lazy_list_inv (head: node_rep) (sub: sub_gname) (obot: option bot_gname)
      (P: node_rep → iProp Σ) : iProp Σ := 
      ∃ (S: gset node_rep) (Skeys: gset Z) (L: list node_rep),
      sub_list_inv head sub P S Skeys L
      ∗
      match obot with
      | None => True
      | Some bot => bot_list_inv bot Skeys
      end.

    Definition levelN (lvl: nat) := nroot .@ "level" .@ lvl.

    Definition is_top_list (head: node_rep) (top bot: sub_gname) : iProp Σ := 
      inv (levelN lvl) (lazy_list_inv head top None (from_top_list bot)).

    Definition is_bot_list (head: node_rep) (Skeys: gset Z) (q: frac)
      (sub: sub_gname) (bot: bot_gname) : iProp Σ := 
      own (s_frac bot) (◯F{q} Skeys)
      ∗
      inv (levelN lvl) (lazy_list_inv head sub (Some bot) from_bot_list).

  End Proofs.
End LazyListInv.