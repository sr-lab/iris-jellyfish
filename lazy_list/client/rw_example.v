From iris.algebra Require Import gset.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import par proofmode.

From SkipList.lazy_list Require Import code.
From SkipList.lazy_list.client Require Import rw_spec.


Module Params <: LAZY_LIST_PARAMS.
  Local Open Scope Z.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
End Params.

Module Import Spec := RWSpec Params.

Definition exampleN := nroot .@ "example".

Definition lazy_list_client : expr := 
  let: "p" := new #() in
    ((add "p" #0;; add "p" #1) ||| (add "p" #1;; add "p" #2));;
    (contains "p" #2 ||| contains "p" #0).

Section Proofs.
  Context `{!heapGS Σ, !rwG Σ, !spawnG Σ}.

  Lemma lazy_list_client_spec :
    {{{ True }}}
      lazy_list_client
    {{{ RET (#true, #true); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".

    unfold lazy_list_client.
    wp_apply (new_spec exampleN); first done.
    iIntros (p Γs) "(#Hset_inv & Hset)".
    iDestruct (rw_inv_alloc_mut exampleN with "Hset") as ">Hinv".
    iDestruct "Hinv" as (Γ) "(#Hinv & Hmut)".

    wp_let. 
    rewrite -(Qp.div_2 1); iDestruct (mut_set_sep with "Hmut") as "(Hmut1 & Hmut2)".
    wp_smart_apply (wp_par (λ _, mut_set _ _ _) (λ _, mut_set _ _ _) with "[Hmut1] [Hmut2]").
    {
      awp_apply (write_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut1"; iModIntro; wp_pures.

      awp_apply (write_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "?"; iModIntro; rewrite left_id_L //.
    }
    { 
      awp_apply (write_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "Hmut2"; iModIntro; wp_pures.

      awp_apply (write_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hmut2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros "?"; iModIntro; rewrite left_id_L //.
    }
    
    iIntros (? ?) "Hmut"; iDestruct (mut_set_join with "Hmut") as "Hmut".
    iNext; wp_pure; wp_pure.
    rewrite gset_op Qp.div_2; iDestruct (mut_to_const with "Hinv Hmut") as ">Hconst".
    rewrite -(Qp.div_2 1); iDestruct (const_set_sep with "Hconst") as "(Hconst1 & Hconst2)".
    wp_smart_apply (wp_par (λ v, ⌜ v = #true ⌝%I) (λ v, ⌜ v = #true ⌝%I) with "[Hconst1] [Hconst2]").
    {
      awp_apply (read_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hconst1"; first (iIntros "?"; iModIntro; iFrame).
      iIntros (b) "(_ & %Hif)"; iModIntro; iPureIntro.
      destruct (b); first done; last set_solver.
    }
    {
      awp_apply (read_spec with "Hinv Hset_inv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iAaccIntro with "Hconst2"; first (iIntros "?"; iModIntro; iFrame).
      iIntros (b) "(_ & %Hif)"; iModIntro; iPureIntro.
      destruct (b); first done; last set_solver.
    }

    iIntros (? ?) "(-> & ->)"; iNext; by iApply "HΦ".
  Qed.
End Proofs.