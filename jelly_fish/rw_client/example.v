From SkipList.atomic Require Import proofmode weakestpre.
From SkipList.lib Require Import argmax.
From SkipList.jelly_fish Require Import code.
From SkipList.jelly_fish.rw_client Require Import spec.

From iris.heap_lang Require Import par notation.


Module Params <: SKIP_LIST_PARAMS.
  Local Open Scope Z.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Definition MAX_HEIGHT := 20.  
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
  Lemma HMAX_HEIGHT : 0 ≤ MAX_HEIGHT.
  Proof. unfold MAX_HEIGHT; lia. Qed.
End Params.

Module Import Spec := RWSpec Params.

Definition exampleN := nroot .@ "example".

Definition example_client : expr := 
  let: "p" := new #() in
    ((put "p" #10 #1 #0;; put "p" #20 #5 #1;; put "p" #10 #3 #2)
    |||
    (put "p" #20 #2 #0;; put "p" #10 #6 #1;; put "p" #10 #4 #2));;
    (get "p" #10 ||| get "p" #20).

Section Proofs.
  Context `{!heapGS Σ, !rwG Σ, !spawnG Σ}.
  Local Open Scope Z.

  Lemma example_client_spec :
    {{{ True }}}
      example_client
    {{{ (v: Z), RET (SOMEV (#v, #2), SOMEV (#5, #1)); ⌜ v = 3 ∨ v = 4 ⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ"; unfold example_client.
    wp_apply new_spec; first done. iIntros (p mΓ) "Hmap".
    iDestruct (rw_inv_alloc_mut exampleN with "Hmap") as "Hinv".
    iMod (fupd_mask_mono with "Hinv") as "Hinv"; first solve_ndisj.
    iDestruct "Hinv" as (Γ) "[#Hinv Hmut]".

    wp_let.
    rewrite -(Qp.div_2 1); iDestruct (mut_map_sep with "Hmut") as "[Hmut1 Hmut2]".
    wp_smart_apply (wp_par (λ _, mut_map _ _ _) (λ _, mut_map _ _ _) with "[Hmut1] [Hmut2]").
    {
      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut1". iModIntro. iExists _, _. iFrame "Hmut1".
      iIntros "Hmut1 _". iModIntro. wp_pures.

      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut1". iModIntro. iExists _, _. iFrame "Hmut1".
      iIntros "Hmut1 _". iModIntro. wp_pures.

      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut1". iModIntro. iExists _, _. iFrame "Hmut1".
      by iIntros.
    }
    {
      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut2". iModIntro. iExists _, _. iFrame "Hmut2".
      iIntros "Hmut2 _". iModIntro. wp_pures.

      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut2". iModIntro. iExists _, _. iFrame "Hmut2".
      iIntros "Hmut2 _". iModIntro. wp_pures.

      awp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut2". iModIntro. iExists _, _. iFrame "Hmut2".
      by iIntros.
    }
    iIntros (? ?) "Hmut". rewrite ?left_id_L.
    iDestruct (mut_map_join with "Hmut") as "Hmut".

    iNext; wp_pure; wp_pure.
    rewrite Qp.div_2; iDestruct (mut_to_const with "Hinv Hmut") as "Hconst".
    iMod (fupd_mask_mono with "Hconst") as "Hconst"; first solve_ndisj.
    rewrite -(Qp.div_2 1); iDestruct (const_map_sep with "Hconst") as "[Hconst1 Hconst2]".
    wp_smart_apply (wp_par 
      (λ v, ⌜ v = SOMEV (#3, #2) ∨ v = SOMEV (#4, #2) ⌝%I) 
      (λ v, ⌜ v = SOMEV (#5, #1) ⌝%I)
    with "[Hconst1] [Hconst2]").
    {
      awp_apply (read_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hconst1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros (opt) "[Hconst1 %Hopt]". iModIntro. iExists _, _. iFrame "Hconst1".
      iIntros "_ _"; iPureIntro.
      destruct Hopt as (vs & v & t & Hprod & Hin & Hopt).
      rewrite argmax_eq in Hprod; inversion Hprod; subst.
      rewrite elem_of_union ?elem_of_singleton in Hin.
      destruct Hin; subst; first (by left); last (by right).
    }
    {
      awp_apply (read_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hconst2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros (opt) "[Hconst2 %Hopt]". iModIntro. iExists _, _. iFrame "Hconst2".
      iIntros "_ _"; iPureIntro.
      destruct Hopt as (vs & v & t & Hprod & Hin & Hopt).
      rewrite comm_L argmax_lt // in Hprod; inversion Hprod; subst.
      rewrite elem_of_singleton in Hin; by subst.
    }
    iIntros (? ?) "[[->|->] ->]"; iNext; iApply "HΦ"; 
      first (by iLeft); last (by iRight).
  Qed.
End Proofs.