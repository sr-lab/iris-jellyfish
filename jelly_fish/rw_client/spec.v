From iris.algebra Require Import frac_auth gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation.

From SkipList.lib Require Import argmax gmap.
From SkipList.atomic Require Import proofmode weakestpre.
From SkipList.jelly_fish Require Import code inv.
From SkipList.jelly_fish.spec Require Import new get put.


Class rwG Σ := RWG { 
  rw_mutG :> inG Σ (frac_authR (gmapR Z (argmax Z)));
  rw_agrG :> inG Σ (frac_authR (agreeR (gmap Z (argmax Z))));
  rw_setG :> skipG Σ
}.

Record rw_gname := mk_rw_gname {
  mut_gname: gname;
  agr_gname: gname
}.

Module RWSpec (Params: SKIP_LIST_PARAMS).
  Import Params.
  Module New := NewSpec Params.
  Module Get := GetSpec Params.
  Module Put := PutSpec Params.
  Export New Get Put.

  Section invariant.
    Context `{!heapGS Σ, !rwG Σ}.
    Local Open Scope Z.

    (* Representation predicate for argmax updates on a map *)
    Fixpoint tset (vl: list tval) (t: Z) : gset Z :=
      match vl with
      | nil => ∅
      | vt :: vl => if (decide (vt.2 < t)) then ∅
                   else {[vt.1]} ∪ tset vl t
      end.
    Definition f_vs (vt: tval * list tval) : argmax Z := 
      prodZ ({[vt.1.1]} ∪ tset vt.2 vt.1.2) vt.1.2.
    Definition ts_map (p: loc) (m: gmap Z (argmax Z)) (mΓ: gmap Z lazy_gname) : iProp Σ := 
      ∃ (m': gmap Z (tval * list tval)), vc_map p m' mΓ ∗ ⌜ m = f_vs <$> m' ⌝.

    Definition mapN := nroot .@ "rw_map".

    (* Public state for concurrent writes *)
    Definition mut_map (m: gmap Z (argmax Z)) (q: frac) (Γ: rw_gname) : iProp Σ := 
      own Γ.(mut_gname) (◯F{q} m).
    Lemma mut_map_sep (m: gmap Z (argmax Z)) (q1 q2: frac) (Γ: rw_gname) :
      mut_map m (q1 + q2) Γ -∗ mut_map m q1 Γ ∗ mut_map m q2 Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; iFrame. Qed.
    Lemma mut_map_join (m1 m2: gmap Z (argmax Z)) (q1 q2: frac) (Γ: rw_gname) :
      mut_map m1 q1 Γ ∗ mut_map m2 q2 Γ -∗ mut_map (m1 ⋅ m2) (q1 + q2) Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; by iCombine "Hmut1 Hmut2" as "Hmut". Qed.

    (* Public state for concurrent reads *)
    Definition const_map (m: gmap Z (argmax Z)) (q: frac) (Γ: rw_gname) : iProp Σ := 
      own Γ.(agr_gname) (◯F{q} (to_agree m)).
    Lemma const_map_sep (m: gmap Z (argmax Z)) (q1 q2: frac) (Γ: rw_gname) :
      const_map m (q1 + q2) Γ -∗ const_map m q1 Γ ∗ const_map m q2 Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; iFrame. Qed.
    Lemma const_map_join (m: gmap Z (argmax Z)) (q1 q2: frac) (Γ: rw_gname) :
      const_map m q1 Γ ∗ const_map m q2 Γ -∗ const_map m (q1 + q2) Γ.
    Proof. iIntros "(Hmut1 & Hmut2)"; by iCombine "Hmut1 Hmut2" as "Hmut". Qed.

    (* Invariant concealing the abstract state of the full map *)
    Definition map_inv (p: loc) (mΓ: gmap Z lazy_gname) (Γ: rw_gname) : iProp Σ :=
      ∃ (m: gmap Z (argmax Z)),
        ts_map p m mΓ
        ∗
        own Γ.(mut_gname) (●F m)
        ∗
        own Γ.(agr_gname) (●F (to_agree m))
        ∗
        (own Γ.(mut_gname) (◯F m) ∨ own Γ.(agr_gname) (◯F (to_agree m))).
    Definition is_map (p: loc) (Γ: rw_gname) : iProp Σ :=
      ∃ (mΓ: gmap Z lazy_gname), inv mapN (map_inv p mΓ Γ).
    Lemma rw_inv_alloc_mut (p: loc) (mΓ: gmap Z lazy_gname) :
      ts_map p ∅ mΓ ={↑mapN}=∗
        ∃ (Γ: rw_gname), is_map p Γ ∗ mut_map ∅ 1 Γ.
    Proof.
      iIntros "Hmap".
      iMod (own_alloc (●F ∅ ⋅ ◯F ∅))
        as (γmut) "[Hmut● Hmut◯]"; first by apply auth_both_valid.
      iMod (own_alloc (●F (to_agree ∅) ⋅ ◯F (to_agree ∅)))
        as (γagr) "[Hagr● Hagr◯]"; first by apply auth_both_valid.
      set (Γ := mk_rw_gname γmut γagr).
      iMod (inv_alloc mapN (↑mapN) (map_inv p mΓ Γ)
        with "[Hmap Hmut● Hagr● Hagr◯]") as "#Hinv".
      { iNext; iExists ∅; iFrame. }
      iModIntro; iExists Γ; iFrame "# ∗"; by iExists mΓ.
    Qed.
    Lemma rw_inv_alloc_const (p: loc) (mΓ: gmap Z lazy_gname) :
      ts_map p ∅ mΓ ={↑mapN}=∗
        ∃ (Γ: rw_gname), is_map p Γ ∗ const_map ∅ 1 Γ.
    Proof.
      iIntros "Hmap".
      iMod (own_alloc (●F ∅ ⋅ ◯F ∅))
        as (γmut) "[Hmut● Hmut◯]"; first by apply auth_both_valid.
      iMod (own_alloc (●F (to_agree ∅) ⋅ ◯F (to_agree ∅)))
        as (γagr) "[Hagr● Hagr◯]"; first by apply auth_both_valid.
      set (Γ := mk_rw_gname γmut γagr).
      iMod (inv_alloc mapN (↑mapN) (map_inv p mΓ Γ)
        with "[Hmap Hmut● Hagr● Hmut◯]") as "#Hinv".
      { iNext; iExists ∅; iFrame. }
      iModIntro; iExists Γ; iFrame "# ∗"; by iExists mΓ.
    Qed.

    (* Helper lemmas for switching between concurrent writes and concurrent reads *)
    Lemma mut_to_const (p: loc) (m: gmap Z (argmax Z)) (Γ: rw_gname) :
      is_map p Γ -∗ mut_map m 1 Γ ={↑mapN}=∗ const_map m 1 Γ.
    Proof.
      rewrite /mut_map/const_map; iIntros "[%mΓ #Hinv] Hmut◯".
      iInv "Hinv" as (m') ">(Hmap & Hmut● & Hagr● & Hagr◯)".
      iDestruct (own_valid_2 with "Hmut● Hmut◯") as %<-%frac_auth_agree_L.
      iDestruct "Hagr◯" as "[Hfalse|Hagr◯]".
      { by iDestruct (own_valid_2 with "Hmut◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iModIntro. iSplitR "Hagr◯"; last (iModIntro; iFrame).
      iNext; iExists m'; iFrame.
    Qed.
    Lemma const_to_mut (p: loc) (m: gmap Z (argmax Z)) (Γ: rw_gname) :
      is_map p Γ -∗ const_map m 1 Γ ={↑mapN}=∗ mut_map m 1 Γ.
    Proof.
      rewrite /mut_map/const_map; iIntros "[%mΓ #Hinv] Hagr◯".
      iInv "Hinv" as (m') ">(Hmap & Hmut● & Hagr● & Hmut◯)".
      iDestruct (own_valid_2 with "Hagr● Hagr◯") as %Heq%frac_auth_agree.
      replace m with m' by rewrite -to_agree_op_valid_L Heq agree_idemp //.
      iDestruct "Hmut◯" as "[Hmut◯|Hfalse]"; last first.
      { by iDestruct (own_valid_2 with "Hagr◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
      iModIntro. iSplitR "Hmut◯"; last (iModIntro; iFrame).
      iNext; iExists m'; iFrame.
    Qed.
  End invariant.

  Section proofs.
    Context `{!heapGS Σ, !rwG Σ}.
    Local Open Scope Z.

    Definition opt_equiv ret opt : iProp Σ :=
      match opt with
      | None => ⌜ ret = NONEV ⌝
      | Some vt => ∃ (vs: gset Z) (v t: Z), 
                     ⌜ vt = prodZ vs t ⌝ ∗ ⌜ v ∈ vs ⌝ ∗ ⌜ ret = SOMEV (#v, #t) ⌝
      end.

    Theorem ts_new_spec : 
      {{{ True }}}
        new #()
      {{{ p mΓ, RET #p; ts_map p ∅ mΓ }}}.
    Proof.
      iIntros (Φ) "_ HΦ". wp_apply new_spec; first done.
      iIntros. iApply "HΦ". iExists ∅.
      rewrite fmap_empty //; by iFrame.
    Qed.

    Theorem ts_get_spec (p: loc) (mΓ: gmap Z lazy_gname)
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<< ∀∀ m, ts_map p m mΓ >>>
        get #p #k @ ∅
      <<< ∃∃ opt, ts_map p m mΓ, RET opt >>>
      {{{ opt_equiv opt (m !! k) }}}.
    Proof.
      iIntros (Φ) "AU". awp_apply get_spec; first done.
      iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
      { 
        iIntros "!> %m Hmap". iDestruct "Hmap" as (m') "[? ?]". 
        iExists m'. iFrame. iIntros. iExists m'. iFrame.
      }
      iIntros (m) "Hmap".
      iDestruct "Hmap" as (m') "[Hmap %Hfmap]".
      iAaccIntro with "Hmap".
      { iIntros "?"; iSplitR ""; last by (iModIntro; iIntros). iExists m'; by iFrame. }
      iIntros "Hmap".

      iModIntro. iExists m'. iFrame. iIntros "Hmap".
      iRight. iExists (opt_to_val (m' !! k)). 
      iSplitR ""; first by (iExists m'; iFrame).
      iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
      iModIntro. iIntros "_". iApply "HΦ".
      rewrite Hfmap lookup_fmap. destruct (m' !! k) as [[[v t] vl]|]; last done.
      iPureIntro; exists ({[v]} ∪ tset vl t), v, t; set_solver.
    Qed.

    Theorem ts_put_spec (p: loc) (k v t: Z) (mΓ: gmap Z lazy_gname)
      (Hrange: INT_MIN < k < INT_MAX) :
      ⊢ <<< ∀∀ m, ts_map p m mΓ >>>
        put #p #k #v #t @ ∅
      <<< ts_map p (m ⋅ {[ k := prodZ {[v]} t]}) mΓ, RET #() >>>
      {{{ True }}}.
    Proof.
      iIntros (Φ) "AU". awp_apply put_spec; first done.
      iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
      { 
        iIntros "!> %m Hmap". iDestruct "Hmap" as (m') "[? ?]". 
        iExists m'. iFrame. iIntros. iExists m'. iFrame.
      }
      iIntros (m) "Hmap".
      iDestruct "Hmap" as (m') "[Hmap %Hfmap]".
      iAaccIntro with "Hmap".
      { iIntros "?"; iSplitR ""; last by (iModIntro; iIntros). iExists m'; by iFrame. }
      iIntros "Hmap".

      iModIntro. iExists (case_map m' k v t). iFrame. iIntros "Hmap".
      assert (m ⋅ {[k := prodZ {[v]} t]} = f_vs <$> case_map m' k v t) 
        as Heq; last (rewrite Heq; clear Heq).
      { 
        rewrite Hfmap. destruct ((f_vs <$> m') !! k) eqn:Hopt.
        + rewrite comm_L -(insert_singleton_op_Some_L _ _ _ _ Hopt).
          rewrite lookup_fmap fmap_Some in Hopt; destruct Hopt as [[vt vl] [Hopt Hf]].
          rewrite /case_map Hopt Hf.
          case_decide.
          - rewrite insert_id // lookup_fmap Hopt fmap_Some.
            exists (vt, vl). split; first done.
            rewrite /f_vs argmax_lt //.
          - rewrite fmap_insert {1 3}/f_vs /=.
            case_decide.
            * rewrite right_id_L comm_L argmax_lt //. 
            * replace t with vt.2 by lia.
              rewrite argmax_eq //.
        + rewrite comm_L -(insert_singleton_op _ _ _ Hopt).
          rewrite lookup_fmap fmap_None in Hopt.
          rewrite /case_map Hopt fmap_insert.
          rewrite {2}/f_vs //= right_id_L //.
      }
      iRight. iFrame. iSplitR ""; first by (iExists (case_map m' k v t); iFrame).
      iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ". done.
    Qed.

    Theorem const_spec (p: loc) (Γ: rw_gname) (q: frac) (m: gmap Z (argmax Z))
      (k: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_map p Γ -∗
      {{{ const_map m q Γ }}}
        get #p #k
      {{{ opt, RET opt; const_map m q Γ ∗ opt_equiv opt (m !! k) }}}.
    Proof.
      iIntros "[%Γl #Hinv] %Φ !> Hconst HΦ".
      iAssert (
      <<< ∀∀ m, const_map m q Γ >>>
        get #p #k @ ↑mapN
      <<< ∃∃ opt, const_map m q Γ, RET opt >>>
      {{{ opt_equiv opt (m !! k) }}}
      )%I as "Hread".
      { 
        iApply (atomic_wp_inv_timeless with "[] Hinv"); first solve_ndisj.
        clear m Φ; iIntros (Φ) "AU".

        awp_apply ts_get_spec; first done.
        iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
        { 
          iIntros "!> %m [Hmap ?]". iDestruct "Hmap" as (m') "[? ?]". 
          iExists m'. iFrame. iIntros. iExists m'. iFrame.
        }
        iIntros (m) "[Hmap Hagr◯]".
        iDestruct "Hmap" as (m') "(Hmap & Hmut● & Hagr● & Hmut◯)".
        iAaccIntro with "Hmap".
        { iIntros "?"; iModIntro; iFrame. iSplitR ""; last by iIntros. iExists m'; iFrame. }
        iIntros (opt) "Hmap".

        iDestruct (own_valid_2 with "Hagr● Hagr◯") as %Heq%frac_auth_included.
        rewrite Some_included_total to_agree_included leibniz_equiv_iff in Heq;
          rewrite Heq; clear Heq.

        iModIntro. iExists m'. iFrame. iIntros "Hmap".
        iRight. iExists opt. 
        iSplitR ""; first (iExists m'; iFrame).
        iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "?".
        iApply fupd_mask_mono; last (by iApply "HΦ"); first solve_ndisj.
      }
      iDestruct (atomic_wp_seq_step with "Hread") as "Hwp".
      iApply ("Hwp" with "Hconst [HΦ]").
      + iNext; iIntros; iApply "HΦ"; by iFrame.
      + iIntros; iExists m; iFrame; by iIntros.
    Qed.

    Theorem mut_spec (p: loc) (Γ: rw_gname) (q: frac) (m: gmap Z (argmax Z))
      (k v t: Z) (Hrange: INT_MIN < k < INT_MAX) :
      is_map p Γ -∗
      {{{ mut_map m q Γ }}}
        put #p #k #v #t
      {{{ RET #(); mut_map (m ⋅ {[ k := prodZ {[v]} t]}) q Γ }}}.
    Proof.
      iIntros "[%Γl #Hinv] %Φ !> Hmut HΦ".
      iAssert (
      <<< ∀∀ m, mut_map m q Γ >>>
        put #p #k #v #t @ ↑mapN
      <<< mut_map (m ⋅ {[ k := prodZ {[v]} t]}) q Γ, RET #() >>>
      {{{ True }}}
      )%I as "Hwrite".
      {
        iApply (atomic_wp_inv_timeless with "[] Hinv"); first solve_ndisj.
        clear m Φ; iIntros (Φ) "AU".

        awp_apply ts_put_spec; first done.
        iApply (aacc_aupd_sub with "[] AU"); first solve_ndisj; first done.
        { 
          iIntros "!> %m [Hmap ?]". iDestruct "Hmap" as (m') "[? ?]". 
          iExists m'. iFrame. iIntros. iExists m'. iFrame.
        }
        iIntros (m) "[Hmap Hmut◯]".
        iDestruct "Hmap" as (m') "(Hmap & Hmut● & Hagr● & Hagr◯)".
        iAaccIntro with "Hmap".
        { iIntros "?"; iModIntro; iFrame. iSplitR ""; last by iIntros. iExists m'; iFrame. }
        iIntros "Hmap".

        iMod (own_update_2 with "Hmut● Hmut◯") as "[Hmut● Hmut◯]".
        { 
          apply frac_auth_update, (op_local_update_discrete _ _ {[ k := prodZ {[v]} t]}). 
          destruct (m' !! k) eqn:Hopt.
          + rewrite -(insert_singleton_op_Some_L _ _ _ _ Hopt).
            by apply insert_valid.
          + rewrite -(insert_singleton_op _ _ _ Hopt).
            by apply insert_valid.
        }
        do 2 rewrite (comm _ {[k := prodZ {[v]} t]} _).
        iDestruct "Hagr◯" as "[Hfalse|Hagr◯]".
        { by iDestruct (own_valid_2 with "Hmut◯ Hfalse") as %[Hfalse%Qp.not_add_le_r _]%frac_auth_frag_valid. }
        iMod (own_update_2 with "Hagr● Hagr◯") as "[Hagr● Hagr◯]".
        { by apply (frac_auth_update_1 _ _ (to_agree (m' ⋅ {[k := prodZ {[v]} t]}))). }

        iModIntro. iExists (m' ⋅ {[k := prodZ {[v]} t]}). iFrame. iIntros "Hmap".
        iRight. iFrame. iSplitR ""; first (iExists (m' ⋅ {[k := prodZ {[v]} t]}); iFrame).
        iIntros "AP". iMod (atomic_post_commit with "AP") as "HΦ".
        iModIntro. iIntros "_".
        iApply fupd_mask_mono; last (by iApply "HΦ"); first solve_ndisj.
      }
      iDestruct (atomic_wp_seq_step with "Hwrite") as "Hwp".
      iApply ("Hwp" with "Hmut [HΦ]").
      + iNext; iIntros; iApply "HΦ"; by iFrame.
      + iIntros; iExists _; iFrame; by iIntros.
    Qed.
  End proofs.
End RWSpec.