From AtomicInvariant.lib Require Import argmax.
From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode.
From AtomicInvariant.examples.jelly_fish Require Import code.
From AtomicInvariant.examples.jelly_fish.rw_client Require Import spec.

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

Definition example_client : expr := 
  let: "p" := newMap #() in
    ((put "p" #10 #1 #0;; put "p" #20 #5 #1;; put "p" #10 #3 #2)
    |||
    (put "p" #20 #2 #0;; put "p" #10 #6 #1;; put "p" #10 #4 #2));;
    (get "p" #10 ||| get "p" #20).

Section Proofs.
  Context `{!heapGS Σ, !rwG Σ, !spawnG Σ}.
  Local Open Scope Z.

  Lemma example_client_spec :
    {{{ emp }}}
      example_client
    {{{ v, RET (SOMEV (#v, #2), SOMEV (#5, #1)); ⌜ v = 3 ∨ v = 4 ⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ"; unfold example_client.
    wp_apply ts_new_spec; first done. iIntros (p mΓ) "Hmap".
    iDestruct (rw_inv_alloc_mut with "Hmap") as "Hinv".
    iMod (fupd_mask_mono with "Hinv") as "Hinv"; first solve_ndisj.
    iDestruct "Hinv" as (Γ) "[#Hinv Hmut]".

    wp_let.
    rewrite -(Qp.div_2 1); iDestruct (mut_map_sep with "Hmut") as "[Hmut1 Hmut2]".
    wp_smart_apply (wp_par (λ _, mut_map _ _ _) (λ _, mut_map _ _ _) with "[Hmut1] [Hmut2]").
    {
      wp_apply (mut_spec with "Hinv Hmut1"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros "Hmut1"; wp_pures.

      wp_apply (mut_spec with "Hinv Hmut1"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros "Hmut1"; wp_pures.

      wp_apply (mut_spec with "Hinv Hmut1"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      by iIntros.
    }
    {
      wp_apply (mut_spec with "Hinv Hmut2"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros "Hmut2"; wp_pures.

      wp_apply (mut_spec with "Hinv Hmut2"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros "Hmut2"; wp_pures.

      wp_apply (mut_spec with "Hinv Hmut2"); 
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
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
      wp_apply (const_spec with "Hinv Hconst1");
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros (opt) "[Hconst1 %Hopt]". iPureIntro.
      destruct Hopt as (vs & v & t & Hprod & Hin & Hopt).
      rewrite argmax_eq in Hprod; inversion Hprod; subst.
      rewrite elem_of_union ?elem_of_singleton in Hin.
      destruct Hin; subst; first (by left); last (by right).
    }
    {
      wp_apply (const_spec with "Hinv Hconst2");
        first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iIntros (opt) "[Hconst2 %Hopt]". iPureIntro.
      destruct Hopt as (vs & v & t & Hprod & Hin & Hopt).
      rewrite comm_L argmax_lt // in Hprod; inversion Hprod; subst.
      rewrite elem_of_singleton in Hin; by subst.
    }
    iIntros (? ?) "[[->|->] ->]"; iNext; iApply "HΦ"; 
      first (by iLeft); last (by iRight).
  Qed.
End Proofs.