From Coq Require Import Lia.

From iris.heap_lang Require Import notation par proofmode.
From iris.algebra Require Import frac.

From SkipList.lib Require Import lock misc.
From SkipList.lazy_list Require Import code.
From SkipList.lazy_list.inv Require Import list_equiv inv.
From SkipList.lazy_list.spec Require Import new contains add.


Local Open Scope Z.

Module Params <: LAZY_LIST_PARAMS.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
End Params.

Module Import New := NewSpec Params.
Module Import Contains := ContainsSpec Params.
Module Import Add := AddSpec Params.

(* Convert a list of Coq ints into a HeapLang tuple *)
Fixpoint L2tuple (L: list Z) : val :=
  match L with
  | nil => NONEV
  | z :: L =>
    SOMEV (#z, L2tuple L)
  end.

Definition addList : val :=
  rec: "add" "lazy" "L" :=
    match: "L" with
      NONE => #()
    | SOME "pair" =>
      let: "key" := Fst "pair" in
      let: "tail" := Snd "pair" in
        add "lazy" "key";;
        "add" "lazy" "tail"
    end.

Definition lazy_list_client (L1 L2: list Z) (key: Z) : expr := 
  let: "lazy" := new #() in
    (addList "lazy" (L2tuple L1) ||| addList "lazy" (L2tuple L2));;
    contains "lazy" #key.

Section Proofs.
  Context `{!heapGS Σ, !gset_list_unionGS Σ, !lockG Σ, !spawnG Σ}.

  Lemma addList_spec (v: val) (S: gset Z) (q: frac) (Γ: lazy_gname) (L: list Z) :
    (∀ (k: Z), k ∈ L → Params.INT_MIN < k < Params.INT_MAX) →
    {{{ is_lazy_list v S q Γ }}}
      addList v (L2tuple L)
    {{{ RET #(); is_lazy_list v (set_list_union S L) q Γ }}}.
  Proof.
    iIntros (Hrange Φ) "Hlazy HΦ".
    iRevert (S L Hrange) "Hlazy HΦ".
    iLöb as "IH".
    iIntros (S L Hrange) "Hlazy HΦ".

    wp_lam. wp_let.
    destruct L as [|key L]; wp_match.
    + iModIntro. iApply "HΦ". iFrame.
    + wp_pures.
      wp_apply (add_spec with "Hlazy").
      { apply Hrange. left. }

      iIntros (b) "Hlazy".
      wp_pures.
      iApply ("IH" with "[%] [$]").
      { intros k Hin. apply Hrange. by right. }

      iNext; iFrame.
  Qed.

  Lemma lazy_list_client_spec (L1 L2: list Z) (key: Z) :
    (Params.INT_MIN < key < Params.INT_MAX) →
    (∀ (k: Z), k ∈ L1 ∨ k ∈ L2 → Params.INT_MIN < k < Params.INT_MAX) →
    {{{ True }}}
      lazy_list_client L1 L2 key
    {{{ (b: bool), RET #b;
      ⌜ if b then key ∈ L1 ∨ key ∈ L2 
             else key ∉ L1 ∧ key ∉ L2 ⌝ 
    }}}.
  Proof.
    iIntros (Hrange Hrange_l Φ) "_ HΦ".

    unfold lazy_list_client.
    wp_apply new_spec; first done.
    iIntros (v Γ) "Hlazy".

    wp_let.
    rewrite -(Qp_div_2 1).
    iDestruct (is_lazy_list_sep with "Hlazy") as "(Hlazy1 & Hlazy2)".

    wp_smart_apply (wp_par (λ _, is_lazy_list v (set_list_union ∅ L1) (1 / 2) Γ)
                           (λ _, is_lazy_list v (set_list_union ∅ L2) (1 / 2) Γ) 
                           with "[Hlazy1] [Hlazy2]").
    + wp_apply (addList_spec with "Hlazy1").
      { intros k Hin. apply Hrange_l. by left. }
      by iIntros.
    + wp_apply (addList_spec with "Hlazy2").
      { intros k Hin. apply Hrange_l. by right. }
      by iIntros.
    + iIntros (v1 v2) "Hlazy".
      rewrite is_lazy_list_join (Qp_div_2 1).
      
      iNext; wp_pures.
      wp_apply (contains_spec with "Hlazy"); first done.
      iIntros (b) "(Hlazy & %Hif)".
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