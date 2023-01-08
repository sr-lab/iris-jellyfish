From iris.algebra Require Import gmap.
From iris.algebra Require Import updates local_updates.

Section stdpp_extra.
  Context `{FinMap K M}.
  Lemma map_union_difference {A} (m1 m2 : M A) :
    m1 ##ₘ m2 → (m1 ∪ m2) ∖ m1 = m2.
  Proof.
    rewrite map_disjoint_spec. intro Hm1m2. apply map_eq. intros i.
    apply option_eq. intros v. specialize (Hm1m2 i).
    unfold union, map_union, union_with, map_union_with.
    rewrite lookup_difference_Some lookup_merge.
    destruct (m1 !! i) as [x'|], (m2 !! i);
      try specialize (Hm1m2 x' v); compute; intuition congruence.
  Qed.
End stdpp_extra.

Section extra.
  Context `{Countable K} {A : cmra}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.
  Implicit Types x y : A.

  Lemma insert_singleton_op_Some m i x y : 
    m !! i = Some x → <[i:=y ⋅ x]> m ≡ {[ i := y ]} ⋅ m.
  Proof.
    intros Hsome; symmetry.
    rewrite -(insert_delete m i x) //.
    rewrite insert_singleton_op; last apply lookup_delete.
    rewrite assoc singleton_op.
    do 2 (rewrite -insert_singleton_op; last apply lookup_delete).
    rewrite (insert_delete m i x) //.
    by rewrite insert_delete_insert.
  Qed.

  Lemma insert_singleton_op_Some_L `{!LeibnizEquiv A} m i x y : 
    m !! i = Some x → <[i:=y ⋅ x]> m = {[ i := y ]} ⋅ m.
  Proof. intros; rewrite -leibniz_equiv_iff insert_singleton_op_Some //. Qed.  

  Lemma insert_singleton_op_empty i x : 
    <[i:=x]> (∅ : gmap K A) = {[ i := x ]} ⋅ ∅.
  Proof. by apply insert_singleton_op. Qed.

  Lemma dom_singleton_op m i x : 
    dom ({[ i := x ]} ⋅ m) = {[i]} ∪ dom m.
  Proof. rewrite dom_op; set_solver. Qed.

  Lemma dom_singleton_op_Some m i x : 
    is_Some (m !! i) → dom ({[ i := x ]} ⋅ m) = dom m.
  Proof. rewrite -elem_of_dom dom_op; set_solver. Qed.
End extra.

(* GMap already exists in stdpp, so we use DMap to avoid ambiguity *)
Inductive gmap_disj K `{Countable K} (A : Type) :=
| DMap : gmap K A → gmap_disj K A
| DMapBot : gmap_disj K A.
Global Arguments DMap {_ _ _ _} _.
Global Arguments DMapBot {_ _ _ _}.

Section gmap_disj.
  Context `{Countable K} {A : Type}.
  Local Arguments op _ _ !_ !_ /.
  Local Arguments cmra_op _ !_ !_ /.
  Local Arguments ucmra_op _ !_ !_ /.

  Global Instance DMap_inj : Inj (=@{gmap K A}) (=) DMap.
  Proof. intros ???. naive_solver. Qed.

  Canonical Structure gmap_disjO := leibnizO (gmap_disj K A).

  Local Instance gmap_disj_valid_instance : Valid (gmap_disj K A) := λ X,
    match X with DMap _ => True | DMapBot => False end.
  Local Instance gmap_disj_unit_instance : Unit (gmap_disj K A) := DMap ∅.
  Local Instance gmap_disj_pcore_instance : PCore (gmap_disj K A) := λ _, Some ε.
  Local Instance gmap_disj_op_instance : Op (gmap_disj K A) := λ X Y,
    match X, Y with
    | DMap X, DMap Y => if decide (X ##ₘ Y) then DMap (X ∪ Y) else DMapBot
    | _, _ => DMapBot
    end.

  Ltac gmap_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal DMap)|done|exfalso]; solve_map_disjoint.

  Lemma gmap_disj_valid_inv_l X Y : ✓ (DMap X ⋅ Y) → ∃ Y', Y = DMap Y' ∧ X ##ₘ Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma gmap_disj_union X Y : X ##ₘ Y → DMap X ⋅ DMap Y = DMap (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma gmap_disj_valid_op X Y : ✓ (DMap X ⋅ DMap Y) ↔ X ##ₘ Y.
  Proof. simpl. case_decide; by split. Qed.
  Lemma gmap_disj_included X Y : DMap X ≼ DMap Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; try gmap_disj_solve. 
      inversion 1; apply map_union_subseteq_l.
    - intros Hsub; pose proof (map_disjoint_difference_l _ _ Hsub).
      exists (DMap (Y ∖ X)). rewrite gmap_disj_union // map_difference_union //.
  Qed.

  Lemma gmap_disj_ra_mixin : RAMixin (gmap_disj K A).
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; gmap_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; try gmap_disj_solve.
      rewrite /op/gmap_disj_op_instance; repeat case_decide; try gmap_disj_solve.
      rewrite assoc //.
    - intros [X1|] [X2|]; try gmap_disj_solve. 
      rewrite /op/gmap_disj_op_instance; repeat case_decide; try gmap_disj_solve.
      rewrite map_union_comm //.
    - intros [X|]; try gmap_disj_solve. 
      simpl; case_decide as Hempty; first rewrite left_id //.
      destruct Hempty; apply map_disjoint_empty_l.
    - exists (DMap ∅); try gmap_disj_solve. 
      simpl; case_decide as Hempty; first rewrite left_id //.
      destruct Hempty; apply map_disjoint_empty_l.
    - intros [X1|] [X2|]; gmap_disj_solve.
  Qed.
  Canonical Structure gmap_disjR := discreteR (gmap_disj K A) gmap_disj_ra_mixin.

  Global Instance gmap_disj_cmra_discrete : CmraDiscrete gmap_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gmap_disj_ucmra_mixin : UcmraMixin (gmap_disj K A).
  Proof. 
    split; try apply _ || done. intros [X|]; try gmap_disj_solve. 
    simpl; case_decide as Hempty; first rewrite left_id //.
    destruct Hempty; apply map_disjoint_empty_l.
  Qed.
  Canonical Structure gmap_disjUR := Ucmra (gmap_disj K A) gmap_disj_ucmra_mixin.

  Local Arguments op _ _ _ _ : simpl never.

  Lemma gmap_disj_dealloc_local_update X Y :
    (DMap X, DMap Y) ~l~> (DMap (X ∖ Y), DMap ∅).
  Proof.
    apply local_update_total_valid=> _ _ /gmap_disj_included HYX.
    rewrite local_update_unital_discrete=> -[Xf|] _ /leibniz_equiv_iff //=.
    rewrite {1}/op /=. case_decide as Hxf; [intros[= ->]|done].
    rewrite map_union_difference ?left_id //.
  Qed.
  Lemma gmap_disj_dealloc_empty_local_update X Z :
    (DMap Z ⋅ DMap X, DMap Z) ~l~> (DMap X, DMap ∅).
  Proof.
    apply local_update_total_valid=> /gmap_disj_valid_op HZX _ _.
    rewrite -(map_union_difference Z X) //.
    rewrite gmap_disj_union; last rewrite map_union_difference //.
    rewrite map_difference_union;
      first apply gmap_disj_dealloc_local_update;
      last apply map_union_subseteq_l.
  Qed.
  Lemma gmap_disj_dealloc_op_local_update X Y Z :
    (DMap Z ⋅ DMap X, DMap Z ⋅ DMap Y) ~l~> (DMap X,DMap Y).
  Proof.
    rewrite -{2}(left_id ε _ (DMap Y)).
    apply op_local_update_frame, gmap_disj_dealloc_empty_local_update.
  Qed.

  Lemma gmap_disj_alloc_op_local_update X Y Z :
    Z ##ₘ X → (DMap X,DMap Y) ~l~> (DMap Z ⋅ DMap X, DMap Z ⋅ DMap Y).
  Proof.
    intros. apply op_local_update_discrete. by rewrite gmap_disj_valid_op.
  Qed.
  Lemma gmap_disj_alloc_local_update X Y Z :
    Z ##ₘ X → (DMap X,DMap Y) ~l~> (DMap (Z ∪ X), DMap (Z ∪ Y)).
  Proof.
    intros. apply local_update_total_valid=> _ _ /gmap_disj_included ?.
    rewrite -!gmap_disj_union //; last by eapply map_disjoint_weaken_r.
    auto using gmap_disj_alloc_op_local_update.
  Qed.
  Lemma gmap_disj_alloc_empty_local_update X Z :
    Z ##ₘ X → (DMap X, DMap ∅) ~l~> (DMap (Z ∪ X), DMap Z).
  Proof.
    intros. rewrite -{2}(right_id_L _ union Z).
    apply gmap_disj_alloc_local_update; set_solver.
  Qed.

  (** Add some basic support for [DMap X = DMap Y], [DMap X ≼ DMap Y], and
  [✓ (DMap X ⋅ DMap Y)] to [set_solver]. There are probably more cases we could
  cover (e.g., involving [DMapBot], or nesting of [⋅]), but it is not clear
  these are useful in practice, nor how to handle them effectively. *)
  Global Instance set_unfold_gmap_eq (X Y : gmap K A) Q :
    SetUnfold (X = Y) Q → SetUnfold (DMap X = DMap Y) Q.
  Proof. intros [?]; constructor. by rewrite (inj_iff _). Qed.
  Global Instance set_unfold_gmap_disj_included (X Y : gmap K A) Q :
    SetUnfold (X ⊆ Y) Q → SetUnfold (DMap X ≼ DMap Y) Q.
  Proof. intros [?]; constructor. by rewrite gmap_disj_included. Qed.
  Global Instance set_unfold_gmap_disj_valid_op (X Y : gmap K A) Q :
    SetUnfold (X ##ₘ Y) Q → SetUnfold (✓ (DMap X ⋅ DMap Y)) Q.
  Proof. intros [?]; constructor. by rewrite gmap_disj_valid_op. Qed.
End gmap_disj.

Global Arguments gmap_disjO _ {_ _}.
Global Arguments gmap_disjR _ {_ _}.
Global Arguments gmap_disjUR _ {_ _}.