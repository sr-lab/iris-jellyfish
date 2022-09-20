From iris.algebra Require Import gmap.
From iris.heap_lang Require Import notation par proofmode.
From iris.algebra Require Import frac.

From SkipList.lib Require Import arg_max.
From SkipList.jellyfish Require Import code.
From SkipList.lib Require Import misc.
From SkipList.jellyfish.inv Require Import list_equiv lazy_inv skip_inv.
From SkipList.jellyfish.spec Require Import new get put.


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
Module Import Get := GetSpec Params.
Module Import Put := PutSpec Params.

(* Convert a list of Coq values into a HeapLang tuple *)
Definition node : Type := Z * Z * Z.
Fixpoint L2tuple (L: list node) : val :=
  match L with
  | nil => NONEV
  | (z, v, h) :: L => SOMEV (#z, #v, #h, L2tuple L)
  end.

Definition nodeKey : val := λ: "l", Fst (Fst "l").
Definition nodeVal : val := λ: "l", Snd (Fst "l").
Definition nodeHeight : val := λ: "l", Snd "l".

Definition putList : val :=
  rec: "put" "skip" "L" "t" :=
    match: "L" with
      NONE => #()
    | SOME "tuple" =>
      let: "node" := Fst "tuple" in
      let: "tail" := Snd "tuple" in
      let: "key" := nodeKey "node" in
      let: "val" := nodeVal "node" in
      let: "height" := nodeHeight "node" in
        put "skip" "key" "val" "t" "height";;
        "put" "skip" "tail" ("t" + #1)
    end.

Definition L1 : list node := (10, 1, 3) :: (20, 2, 6) :: (10, 3, 4) :: nil.
Definition L2 : list node := (20, 5, 2) :: (10, 2, 5) :: (10, 6, 4) :: nil.
Definition skip_list_client : expr := 
  let: "skip" := new #() in
    (putList "skip" (L2tuple L1) #0 ||| putList "skip" (L2tuple L2) #0);;
    (get "skip" #10, get "skip" #20).

Section Proofs.
  Context `{!heapGS Σ, !skipGS Σ, !lockG Σ, !spawnG Σ}.

  Lemma skip_list_client_spec :
    {{{ True }}}
      skip_list_client
    {{{ (v: Z), RET (SOMEV (#v, #2), SOMEV (#2, #1));
      ⌜ v = 3 ∨ v = 6 ⌝ 
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".

    unfold skip_list_client.
    wp_apply new_spec; first done.
    iIntros (v bot subs) "Hskip".

    wp_let.
    rewrite -(Qp.div_2 1).
    iDestruct (is_skip_list_sep with "Hskip") as "(Hskip1 & Hskip2)".

    wp_smart_apply (wp_par (λ _, is_skip_list v ({[20 := prodZ {[2]} 1]} ⋅ {[10 := prodZ {[3]} 2]}) (1 / 2) bot subs) 
                           (λ _, is_skip_list v ({[10 := prodZ {[6]} 2]} ⋅ {[20 := prodZ {[5]} 0]}) (1 / 2) bot subs) 
                           with "[Hskip1] [Hskip2]").
    + do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip1").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".
      rewrite left_id_L.

      wp_pures. assert (0 + 1 = 1) as -> by lia.
      do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".
      rewrite comm_L.
      
      wp_pures. assert (1 + 1 = 2) as -> by lia.
      do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".
      rewrite -assoc_L singleton_op arg_max_lt //.

      wp_pures. wp_lam. wp_pures.
      by iModIntro.
    + do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip2").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".
      rewrite left_id_L.

      wp_pures. assert (0 + 1 = 1) as -> by lia.
      do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".

      wp_pures. assert (1 + 1 = 2) as -> by lia.
      do 4 (wp_lam; wp_pures).
      wp_apply (put_spec with "Hskip").
      { rewrite /Params.INT_MIN /Params.INT_MAX //. }
      { rewrite /Params.MAX_HEIGHT //. }
      iIntros "Hskip".
      rewrite -assoc_L singleton_op arg_max_lt // comm_L.

      wp_pures. wp_lam. wp_pures.
      by iModIntro.
    + iIntros (v1 v2) "Hskip".
      rewrite is_skip_list_join (Qp.div_2 1).

      rewrite -gmap_op. 
      rewrite -assoc_L comm_L assoc_L singleton_op arg_max_eq.
      rewrite -assoc_L singleton_op arg_max_lt //.

      iNext; wp_pures.
      wp_apply (get_spec with "Hskip"); first done.
      iIntros (opt2) "(Hskip & %Hopt)".
      destruct Hopt as [[_ Hfalse]|Hsome2].
      {
        exfalso. rewrite lookup_op op_None lookup_singleton in Hfalse.
        destruct Hfalse; congruence.
      }

      wp_apply (get_spec with "Hskip"); first done.
      iIntros (opt1) "(Hskip & %Hopt)".
      destruct Hopt as [[_ Hfalse]|Hsome1].
      {
        exfalso. rewrite lookup_op op_None lookup_singleton in Hfalse.
        destruct Hfalse; congruence.
      }

      destruct Hsome1 as [t1 [z1 [S1 [-> [Hsome1 Hin1]]]]].
      rewrite lookup_op lookup_singleton lookup_singleton_ne // right_id_L in Hsome1.
      inversion Hsome1; subst.

      destruct Hsome2 as [t2 [z2 [S2 [-> [Hsome2 Hin2]]]]].
      rewrite lookup_op lookup_singleton lookup_singleton_ne // left_id_L in Hsome2.
      inversion Hsome2; subst.
      rewrite elem_of_singleton in Hin2; subst.

      wp_pures; iModIntro.
      iApply "HΦ". iPureIntro.
      rewrite elem_of_union in Hin1.
      destruct Hin1 as [Hin1|Hin1].
      - rewrite elem_of_singleton in Hin1. by left.
      - rewrite elem_of_singleton in Hin1. by right.
  Qed.

End Proofs.