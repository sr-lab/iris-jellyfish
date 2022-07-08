From Coq Require Import Lia.

From iris.heap_lang Require Import notation par proofmode.
From iris.algebra Require Import frac.

From SkipList.lib Require Import lock misc.
From SkipList.skip_list.arrays Require Import code.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import new contains add.


Local Open Scope Z.

Module Params <: SKIP_LIST_PARAMS.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Definition MAX_HEIGHT := 20%nat.  
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
End Params.

Module Import New := NewSpec Params.
Module Import Contains := ContainsSpec Params.
Module Import Add := AddSpec Params.

Notation node := (prod Z nat).
Definition keys (L: list node) : list Z := map fst L.
Definition heights (L: list node) : list nat := map snd L.

(* Convert a list of Coq ints into a HeapLang tuple *)
Fixpoint L2tuple (L: list node) : val :=
  match L with
  | nil => NONEV
  | (z, h) :: L => SOMEV (#z, #h, L2tuple L)
  end.

Definition addList : val :=
  rec: "add" "skip" "L" :=
    match: "L" with
      NONE => #()
    | SOME "tuple" =>
      let: "key" := Fst (Fst "tuple") in
      let: "height" := Snd (Fst "tuple") in
      let: "tail" := Snd "tuple" in
        add "skip" "key" "height";;
        "add" "skip" "tail"
    end.

Definition skip_list_client (L1 L2: list node) (key: Z) : expr := 
  let: "skip" := new #() in
    (addList "skip" (L2tuple L1) ||| addList "skip" (L2tuple L2));;
    contains "skip" #key.

Section Proofs.
  Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ, !spawnG Σ}.

  Lemma addList_spec (v: val) (S: gset Z) (q: frac) 
    (bot: bot_gname) (subs: list sub_gname) (L: list node) :
    (∀ (k: Z), k ∈ keys L → Params.INT_MIN < k < Params.INT_MAX) →
    (∀ (h: nat), h ∈ heights L → h ≤ Params.MAX_HEIGHT) →
    {{{ is_skip_list v S q bot subs }}}
      addList v (L2tuple L)
    {{{ RET #(); is_skip_list v (set_list_union S (keys L)) q bot subs }}}.
  Proof.
    iIntros (Hk_range Hh_range Φ) "Hskip HΦ".
    iRevert (S L Hk_range Hh_range) "Hskip HΦ".
    iLöb as "IH".
    iIntros (S L Hk_range Hh_range) "Hskip HΦ".

    wp_lam. wp_let.
    destruct L as [|pair L].
    + wp_match. iModIntro. iApply "HΦ". iFrame.
    + destruct pair as [key height]. wp_pures. 
      
      wp_apply (add_spec with "Hskip").
      { apply Hk_range. left. }
      { apply Hh_range. left. }

      iIntros (b) "Hskip".
      wp_pures.
      iApply ("IH" with "[%] [%] [$]").
      { intros k Hin. apply Hk_range. by right. }
      { intros h Hin. apply Hh_range. by right. }

      iNext; iFrame.
  Qed.

  Lemma skip_list_client_spec (L1 L2: list node) (key: Z) :
    (Params.INT_MIN < key < Params.INT_MAX) →
    (∀ (k: Z), k ∈ keys L1 ∨ k ∈ keys L2 → Params.INT_MIN < k < Params.INT_MAX) →
    (∀ (h: nat), h ∈ heights L1 ∨ h ∈ heights L2 → h ≤ Params.MAX_HEIGHT) →
    {{{ True }}}
      skip_list_client L1 L2 key
    {{{ (b: bool), RET #b;
      ⌜ if b then key ∈ keys L1 ∨ key ∈ keys L2 
             else key ∉ keys L1 ∧ key ∉ keys L2 ⌝ 
    }}}.
  Proof.
    iIntros (Hrange Hk_range Hh_range Φ) "_ HΦ".

    unfold skip_list_client.
    wp_apply new_spec; first done.
    iIntros (v bot subs) "Hskip".

    wp_let.
    rewrite -(Qp_div_2 1).
    iDestruct (is_skip_list_sep with "Hskip") as "(Hskip1 & Hskip2)".

    wp_smart_apply (wp_par (λ _, is_skip_list v (set_list_union ∅ (keys L1)) (1 / 2) bot subs)
                           (λ _, is_skip_list v (set_list_union ∅ (keys L2)) (1 / 2) bot subs) 
                           with "[Hskip1] [Hskip2]").
    + wp_apply (addList_spec with "Hskip1").
      { intros k Hin. apply Hk_range. by left. }
      { intros h Hin. apply Hh_range. by left. }
      by iIntros.
    + wp_apply (addList_spec with "Hskip2").
      { intros k Hin. apply Hk_range. by right. }
      { intros h Hin. apply Hh_range. by right. }
      by iIntros.
    + iIntros (v1 v2) "Hskip".
      rewrite is_skip_list_join (Qp_div_2 1).
      
      iNext; wp_pures.
      wp_apply (contains_spec with "Hskip"); first done.
      iIntros (b) "(Hskip & %Hif)".
      iApply "HΦ". iPureIntro. 
      
      destruct b.
      - rewrite elem_of_union in Hif.
        destruct Hif as [Hin1 | Hin2].
        * left. by apply in_empty_set_list_union.
        * right. by apply in_empty_set_list_union.
      - rewrite elem_of_union in Hif.
        split; intros Hfalse; destruct Hif.
        * left. by apply in_empty_set_list_union.
        * right. by apply in_empty_set_list_union.
  Qed.

End Proofs.