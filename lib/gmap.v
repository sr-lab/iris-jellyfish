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