From stdpp Require Import gmap.
From iris.algebra Require Export local_updates proofmode_classes.


Inductive argmax `{Countable A} :=
| prodZ : gset A → Z → argmax
| botZ : argmax.
Global Arguments argmax _ {_ _}.

Section cmra.
  Context `{Countable A}.
  Local Open Scope Z.
  Local Arguments op _ _ !_ !_ /.
  Local Arguments cmra_op _ !_ !_ /.
  Local Arguments ucmra_op _ !_ !_ /.

  Canonical Structure argmax0 := leibnizO (argmax A).

  Local Instance argmax_valid_instance : Valid (argmax A) := λ _, True.
  Local Instance argmax_unit_instance : Unit (argmax A) := botZ.
  Local Instance argmax_pcore_instance : PCore (argmax A) := Some.
  Local Instance argmax_op_instance : Op (argmax A) := λ n m,
    match m, n with
    | prodZ a i, prodZ b j => if (decide (i = j)) then prodZ (a ∪ b) i
                              else if (decide (i < j)) then n else m
    | botZ, _ => n
    | _, botZ => m
    end.

  Global Instance : IdemP (=@{argmax A}) (⋅).
  Proof. intros [a i|]; rewrite ///op/argmax_op_instance idemp_L; by case_decide. Qed.

  Lemma argmax_ra_mixin : RAMixin (argmax A).
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    + intros [a i|] [b j|] [c k|]; rewrite //?/op/argmax_op_instance;
        repeat case_decide; try done; try lia; rewrite assoc_L //.
    + intros [a i|] [b j|]; rewrite //?/op/argmax_op_instance;
        repeat case_decide; try done; try lia; subst; rewrite comm_L //.
    + intros x; rewrite idemp //.
  Qed.
  Canonical Structure argmaxR : cmra := discreteR (argmax A) argmax_ra_mixin.

  Global Instance argmax_cmra_discrete : CmraDiscrete argmaxR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma argmax_ucmra_mixin : UcmraMixin (argmax A).
  Proof. split; try apply _ || done. intros [x|]; done. Qed.
  Canonical Structure argmaxUR : ucmra := Ucmra (argmax A) argmax_ucmra_mixin.

  Global Instance argmax_core_id (x : argmax A) : CoreId x.
  Proof. by constructor. Qed.

  Lemma argmax_included (x y: argmax A) : x ≼ y ↔ x ⋅ y = y.
  Proof.
    split; last by exists y.
    intros [z ->]; rewrite assoc idemp //.
  Qed.

  Lemma argmax_lt (a b : gset A) (i j : Z)  :
    i < j → prodZ a i ⋅ prodZ b j = prodZ b j.
  Proof. intros; rewrite /op/argmax_op_instance; repeat case_decide; try lia; done. Qed.
  Lemma argmax_eq (a b : gset A) (i : Z) :
    prodZ a i ⋅ prodZ b i = prodZ (a ∪ b) i.
  Proof. rewrite comm_L /op/argmax_op_instance; by case_decide. Qed.
  Lemma argmax_bot (m : argmax A) :
    m ⋅ botZ = m.
  Proof. by destruct m. Qed.

  Lemma argmax_local_update (x y z : argmax A) :
    (x,y) ~l~> (z ⋅ x,z ⋅ y).
  Proof. by apply op_local_update. Qed.

  Global Instance argmax_is_op (x y : argmax A) :
    IsOp (x ⋅ y) x y.
  Proof. done. Qed.
End cmra.

Global Arguments argmaxR _ {_ _}.
Global Arguments argmaxUR _ {_ _}.