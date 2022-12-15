From stdpp Require Import gmap.
From iris.algebra Require Export local_updates proofmode_classes.


Section arg_max.
  Context `{Countable A}.
  Local Open Scope Z.

  Inductive argmax :=
  | prodZ : gset A → Z → argmax
  | botZ : argmax.

  Canonical Structure argmax0 := leibnizO argmax.

  Definition args (p: argmax) : gset A :=
    match p with
    | prodZ a i => a
    | botZ => ∅
    end.

  Definition arg_max (m n: argmax) : argmax :=
    match m, n with
    | prodZ a i, prodZ b j => if (decide (i = j)) then prodZ (a ∪ b) i
                              else if (decide (i < j)) then n else m
    | botZ, _ => n
    | _, botZ => m
    end.

  Lemma arg_max_id :
    ∀ m : argmax, arg_max m m = m.
  Proof.
    intros m.
    destruct m as [a i|].
    + rewrite /arg_max.
      destruct (decide (i = i)); last done.
      by assert (a ∪ a = a) as -> by set_solver.
    + rewrite /arg_max //.
  Qed.

  Lemma arg_max_comm :
    ∀ m n : argmax, arg_max m n = arg_max n m.
  Proof.
    intros m n.
    destruct m as [a i|]; destruct n as [b j|]; rewrite /arg_max //.

    destruct (decide (i = j)); simpl;
    destruct (decide (j = i)); simpl;
    try congruence; subst.
    { rewrite comm_L //. }

    destruct (decide (i < j));
    destruct (decide (j < i));
    try lia; done.
  Qed.

  Lemma arg_max_assoc :
    ∀ m n p : argmax, arg_max m (arg_max n p) = arg_max (arg_max m n) p.
  Proof.
    intros m n p.
    destruct m as [a i|]; 
    destruct n as [b j|]; 
    destruct p as [c k|]; 
    rewrite /arg_max //.

    + destruct (decide (j = k)) eqn: Hjk;
      destruct (decide (i = j)) eqn:Hij; 
      destruct (decide (i = k)) eqn:Hik;
      try congruence;
      destruct (decide (j < k)) eqn: Hjk';
      destruct (decide (i < j)); 
      destruct (decide (i < k));
      try lia; 
      rewrite ?Hjk ?Hij ?Hik ?Hjk' //.
      rewrite assoc_L //.
    + destruct (decide (i = j));
      destruct (decide (i < j));
      done.
  Qed.
End arg_max.
Global Arguments argmax _ {_ _}.

Section cmra.
  Context `{Countable A}.
  Local Open Scope Z.

  Local Instance arg_max_unit_instance : Unit (argmax A) := botZ.
  Local Instance arg_max_valid_instance : Valid (argmax A) := λ _, True.
  Local Instance arg_max_validN_instance : ValidN (argmax A) := λ _ _, True.
  Local Instance arg_max_pcore_instance : PCore (argmax A) := Some.
  Local Instance arg_max_op_instance : Op (argmax A) := λ n m, arg_max n m.
  Definition arg_max_op x y : x ⋅ y = arg_max x y := eq_refl.

  Lemma arg_max_ra_mixin : RAMixin (argmax A).
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    + intros x y z. repeat rewrite arg_max_op.
      rewrite arg_max_assoc //.
    + intros x y. by rewrite arg_max_op arg_max_comm.
    + intros x. by rewrite arg_max_op arg_max_id.
  Qed.
  Canonical Structure arg_maxR : cmra := discreteR (argmax A) arg_max_ra_mixin.

  Global Instance arg_max_cmra_discrete : CmraDiscrete arg_maxR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma arg_max_ucmra_mixin : UcmraMixin (argmax A).
  Proof. split; try apply _ || done. Qed.
  Canonical Structure arg_maxUR : ucmra := Ucmra (argmax A) arg_max_ucmra_mixin.

  Global Instance arg_max_core_id (x : argmax A) : CoreId x.
  Proof. by constructor. Qed.

  Lemma arg_max_included (x y: argmax A) : x ≼ y ↔ arg_max x y = y.
  Proof.
    split.
    - intros [z ->].
      rewrite arg_max_assoc arg_max_id //.
    - by exists y.
  Qed.

  Lemma arg_max_lt (a b : gset A) (i j : Z)  :
    i < j → prodZ a i ⋅ prodZ b j = prodZ b j.
  Proof.
    intros. rewrite arg_max_op /arg_max.
    destruct (decide (i = j)); first lia.
    destruct (decide (i < j)); last lia.
    done.
  Qed.

  Lemma arg_max_eq (a b : gset A) (i : Z) :
    prodZ a i ⋅ prodZ b i = prodZ (a ∪ b) i.
  Proof.
    rewrite arg_max_op /arg_max.
    by destruct (decide (i = i)).
  Qed.

  Lemma arg_max_bot (m : argmax A) :
    m ⋅ botZ = m.
  Proof.
    rewrite arg_max_op /arg_max.
    by destruct m.
  Qed.

  Lemma arg_max_args (a b : gset A) (i j : Z) :
    args (prodZ a i ⋅ prodZ b j) ⊆ a ∪ b.
  Proof.
    destruct (decide (i = j)) as [<-|]; first by rewrite arg_max_eq.
    destruct (decide (i < j)); first (rewrite arg_max_lt //; apply union_subseteq_r).
    assert (j < i) by lia; rewrite comm arg_max_lt //; apply union_subseteq_l.
  Qed.

  Lemma arg_max_local_update (x y z : argmax A) :
    (x,y) ~l~> (z ⋅ x,z ⋅ y).
  Proof. by apply op_local_update. Qed.

  Global Instance : IdemP (=@{argmax A}) (⋅).
  Proof. intros x. rewrite arg_max_op arg_max_id //. Qed.

  Global Instance arg_max_is_op (x y : argmax A) :
    IsOp (x ⋅ y) x y.
  Proof. done. Qed.
End cmra.
Global Arguments arg_maxR _ {_ _}.
Global Arguments arg_maxUR _ {_ _}.