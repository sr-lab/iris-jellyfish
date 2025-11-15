From AtomicInvariant.atomic Require Import triple.
From iris.heap_lang Require Import proofmode.
From AtomicInvariant.examples.lazy_list Require Import code.
From AtomicInvariant.examples.lazy_list.rw_client Require Import spec.

From iris.heap_lang Require Import par notation.


Module Params <: LAZY_LIST_PARAMS.
  Local Open Scope Z.
  Definition INT_MIN := -1000.
  Definition INT_MAX := 1000.
  Lemma HMIN_MAX : INT_MIN < INT_MAX.
  Proof. unfold INT_MIN, INT_MAX; lia. Qed.
End Params.

Module Import Spec := RWSpec Params.

Definition exampleN := nroot .@ "example".

Definition example_client : expr := 
  let: "p" := new #() in
    ((add "p" #0;; add "p" #1) ||| (add "p" #1;; add "p" #2));;
    (contains "p" #2 ||| contains "p" #0).

Section Proofs.
  Context `{!heapGS Σ, !rwG Σ, !spawnG Σ}.

  Lemma example_client_spec :
    {{{ emp }}}
      example_client
    {{{ RET (#true, #true); emp }}}.
  Proof.
    iIntros (Φ) "_ HΦ".

    unfold example_client.
    wp_apply new_spec; first done.
    iIntros (p Γl) "Hset".
    iDestruct (rw_inv_alloc_mut exampleN with "Hset") as ">Hinv".
    iDestruct "Hinv" as (Γ) "[#Hinv Hmut]".

    wp_let. 
    rewrite -(Qp.div_2 1); iDestruct (mut_set_sep with "Hmut") as "[Hmut1 Hmut2]".
    wp_smart_apply (wp_par (λ _, mut_set _ _ _) (λ _, mut_set _ _ _) with "[Hmut1] [Hmut2]").
    {
      wp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj. do 2 (iExists _, _; iFrame; iIntros).
      wp_pures.

      wp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj. do 2 (iExists _, _; iFrame; iIntros).
      done.
    }
    { 
      wp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj. do 2 (iExists _, _; iFrame; iIntros).
      wp_pures.

      wp_apply (write_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj. do 2 (iExists _, _; iFrame; iIntros).
      done.
    }
    iIntros (? ?) "Hmut". rewrite ?left_id_L.
    iDestruct (mut_set_join with "Hmut") as "Hmut".

    iNext; wp_pure; wp_pure.
    rewrite Qp.div_2; iDestruct (mut_to_const with "Hinv Hmut") as ">Hconst".
    rewrite -(Qp.div_2 1); iDestruct (const_set_sep with "Hconst") as "[Hconst1 Hconst2]".
    wp_smart_apply (wp_par (λ v, ⌜ v = #true ⌝%I) (λ v, ⌜ v = #true ⌝%I) with "[Hconst1] [Hconst2]").
    {
      wp_apply (read_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj.
      iExists _, _. iFrame. iIntros (b) "[? %]".
      iExists _, _. iFrame. iIntros.
      iIntros; iPureIntro. destruct (b); first done; last set_solver.
    }
    {
      wp_apply (read_spec with "Hinv"); first rewrite /Params.INT_MIN/Params.INT_MAX//.
      iApply ainv_intro; first solve_ndisj.
      iExists _, _. iFrame. iIntros (b) "[? %]".
      iExists _, _. iFrame. iIntros.
      iIntros; iPureIntro. destruct (b); first done; last set_solver.
    }
    iIntros (? ?) "[-> ->]"; iNext; by iApply "HΦ".
  Qed.
End Proofs.