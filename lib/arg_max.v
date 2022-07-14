From stdpp Require Import gmap.
From iris.algebra Require Export cmra local_updates proofmode_classes.


Local Open Scope Z.

Section arg_max.
  Context `{Countable V}.

  Definition prodZ (V: Type) `{Countable V} : Type := gset V * Z.
  Canonical Structure prodZ0 := leibnizO (prodZ V).

  Definition arg_max (n m: prodZ V) : prodZ V :=
    if (decide (n.2 = m.2)) then (n.1 ∪ m.1, n.2)
    else if (decide (n.2 < m.2)) then m else n.

  Lemma arg_max_id :
    ∀ n : prodZ V, arg_max n n = n.
  Proof.
    intros (n1&n2).
    unfold arg_max; simpl.
    destruct (decide (n2 = n2));
    destruct (decide (n2 < n2));
    try done;
    by assert (n1 ∪ n1 = n1) as -> by set_solver.
  Qed.

  Lemma arg_max_comm :
    ∀ m n : prodZ V, arg_max m n = arg_max n m.
  Proof.
    intros (m1&m2) (n1&n2).
    unfold arg_max; simpl.
    destruct (decide (m2 = n2)); simpl;
    destruct (decide (n2 = m2)); simpl;
    try congruence;
    destruct (decide (m2 < n2));
    destruct (decide (n2 < m2)); 
    try lia; try congruence; subst.
    by assert (m1 ∪ n1 = n1 ∪ m1) as -> by set_solver.
  Qed.

  Lemma arg_max_assoc :
    ∀ m n p : prodZ V, arg_max m (arg_max n p) = arg_max (arg_max m n) p.
  Proof.
    intros (m1&m2) (n1&n2) (p1&p2). 
    unfold arg_max; simpl.
    destruct (decide (n2 = p2));
    destruct (decide (n2 < p2)); simpl;
    destruct (decide (m2 = n2));
    destruct (decide (m2 < n2)); simpl;
    destruct (decide (m2 = p2));
    destruct (decide (m2 < p2)); simpl;
    destruct (decide (n2 = p2));
    destruct (decide (n2 < p2)); simpl;
    try done; try lia.
    by assert (m1 ∪ (n1 ∪ p1) = m1 ∪ n1 ∪ p1) as -> by set_solver.
  Qed.
End arg_max.

Section cmra.
  Context `{Countable V}.

  Local Instance arg_max_valid_instance : Valid (prodZ V) := λ _, True.
  Local Instance arg_max_pcore_instance : PCore (prodZ V) := Some.
  Local Instance arg_max_op_instance : Op (prodZ V) := λ n m, arg_max n m.
  Definition arg_max_op x y : x ⋅ y = arg_max x y := eq_refl.

  Lemma arg_max_ra_mixin : RAMixin (prodZ V).
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    - intros x y z. repeat rewrite arg_max_op.
      rewrite arg_max_assoc //.
    - intros x y. by rewrite arg_max_op arg_max_comm.
    - intros x. by rewrite arg_max_op arg_max_id.
  Qed.
  Canonical Structure arg_maxR : cmra := discreteR (prodZ V) arg_max_ra_mixin.

  Global Instance arg_max_cmra_discrete : CmraDiscrete arg_maxR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance arg_max_core_id (x : prodZ V) : CoreId x.
  Proof. by constructor. Qed.

  Lemma arg_max_included (x y: prodZ V) : x ≼ y ↔ arg_max x y = y.
  Proof.
    split.
    - intros [z ->].
      rewrite arg_max_assoc arg_max_id //.
    - by exists y.
  Qed.

  Lemma arg_max_eq (x y: prodZ V) :
    x.2 < y.2 → x ⋅ y = y.
  Proof.
    intros. rewrite arg_max_op.
    destruct x as [x1 x2]; destruct y as [y1 y2].
    unfold arg_max; simpl in *.
    destruct (decide (x2 = y2)); first lia.
    destruct (decide (x2 < y2)); last lia.
    done.
  Qed.

  Lemma arg_max_frame (x y z: prodZ V) :
     x ≼ z → y ≼ z → (z,z) = (z ⋅ x,z ⋅ y).
  Proof.
    repeat rewrite arg_max_included arg_max_op.
    intros Hxz Hyz.
    rewrite arg_max_comm in Hxz.
    rewrite arg_max_comm in Hyz.
    rewrite Hxz Hyz //.
  Qed.

  Lemma arg_max_local_update (x y z : prodZ V) :
    x ⋅ z = z → (x,y) ~l~> (z,z).
  Proof.
    intros Hxz.
    apply local_update_valid.
    intros _ _ [Heq | Hyx].
    + rewrite -Heq -Hxz comm.
      by apply op_local_update_discrete.
    + rewrite -arg_max_included in Hxz.
      rewrite (arg_max_frame x y z).
      - apply op_local_update_discrete. done.
      - done.
      - rewrite arg_max_included.
        rewrite arg_max_included in Hyx.
        rewrite arg_max_included in Hxz.
        rewrite -Hxz arg_max_assoc Hyx //.
  Qed.

  Global Instance : IdemP (=@{prodZ V}) (⋅).
  Proof. intros x. rewrite arg_max_op arg_max_id //. Qed.

  Global Instance arg_max_is_op (x y : prodZ V) :
    IsOp (x ⋅ y) x y.
  Proof. done. Qed.
End cmra.

Global Arguments arg_maxR _ {_ _}.