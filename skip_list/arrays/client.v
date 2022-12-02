From iris.heap_lang Require Import notation par proofmode.
From iris.algebra Require Import frac.

From SkipList.skip_list.arrays Require Import code.
From SkipList.lib Require Import misc.
From SkipList.skip_list.arrays.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.skip_list.arrays.spec Require Import new contains add.


Local Open Scope Z.

Module Params <: SKIP_LIST_PARAMS.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Definition MAX_HEIGHT := 20.  
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
  Lemma HMAX_HEIGHT : 0 ≤ MAX_HEIGHT.
  Proof. unfold MAX_HEIGHT; lia. Qed.
End Params.

Module Import New := NewSpec Params.
Module Import Contains := ContainsSpec Params.
Module Import Add := AddSpec Params.

(* Convert a list of Coq ints into a HeapLang tuple *)
Fixpoint L2tuple (L: list Z) : val :=
  match L with
  | nil => NONEV
  | z :: L => SOMEV (#z, L2tuple L)
  end.

Definition addList : val :=
  rec: "add" "skip" "L" :=
    match: "L" with
      NONE => #()
    | SOME "tuple" =>
      let: "key" := Fst "tuple" in
      let: "tail" := Snd "tuple" in
        add "skip" "key";;
        "add" "skip" "tail"
    end.

Definition skip_list_client (L1 L2: list Z) (key: Z) : expr := 
  let: "skip" := new #() in
    (addList "skip" (L2tuple L1) ||| addList "skip" (L2tuple L2));;
    contains "skip" #key.

Section Proofs.
  Context `{!heapGS Σ, !skipGS Σ, !lockG Σ, !spawnG Σ}.

  Lemma addList_spec (p: loc) (S: gset Z) (q: frac) 
    (bot: bot_gname) (subs: list sub_gname) (L: list Z) :
    (∀ (k: Z), k ∈ L → Params.INT_MIN < k < Params.INT_MAX) →
    {{{ is_skip_list p S q bot subs }}}
      addList #p (L2tuple L)
    {{{ RET #(); is_skip_list p (set_list_union S L) q bot subs }}}.
  Proof.
    iIntros (Hk_range Φ) "Hskip HΦ".
    iRevert (S L Hk_range) "Hskip HΦ".
    iLöb as "IH".
    iIntros (S L Hk_range) "Hskip HΦ".

    wp_lam. wp_let.
    destruct L as [|z L].
    + wp_match. iModIntro. iApply "HΦ". iFrame.
    + wp_pures. 
      
      wp_apply (add_spec with "Hskip").
      { apply Hk_range. left. }
      iIntros "Hskip".

      wp_pures.
      iApply ("IH" with "[%] [$]").
      { intros k Hin. apply Hk_range. by right. }
      iNext; iFrame.
  Qed.

  Lemma skip_list_client_spec (L1 L2: list Z) (key: Z) :
    (Params.INT_MIN < key < Params.INT_MAX) →
    (∀ (k: Z), k ∈ L1 ∨ k ∈ L2 → Params.INT_MIN < k < Params.INT_MAX) →
    {{{ True }}}
      skip_list_client L1 L2 key
    {{{ (b: bool), RET #b;
      ⌜ if b then key ∈ L1 ∨ key ∈ L2 
             else key ∉ L1 ∧ key ∉ L2 ⌝ 
    }}}.
  Proof.
    iIntros (Hrange Hk_range Φ) "_ HΦ".

    unfold skip_list_client.
    wp_apply new_spec; first done.
    iIntros (p bot subs) "Hskip".

    wp_let.
    rewrite -(Qp.div_2 1).
    iDestruct (is_skip_list_sep with "Hskip") as "(Hskip1 & Hskip2)".

    wp_smart_apply (wp_par (λ _, is_skip_list p (set_list_union ∅ L1) (1 / 2) bot subs)
                           (λ _, is_skip_list p (set_list_union ∅ L2) (1 / 2) bot subs) 
                           with "[Hskip1] [Hskip2]").
    + wp_apply (addList_spec with "Hskip1").
      { intros k Hin. apply Hk_range. by left. }
      by iIntros.
    + wp_apply (addList_spec with "Hskip2").
      { intros k Hin. apply Hk_range. by right. }
      by iIntros.
    + iIntros (v1 v2) "Hskip".
      rewrite is_skip_list_join (Qp.div_2 1).
      
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