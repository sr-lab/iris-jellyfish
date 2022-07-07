From iris.algebra Require Import local_updates gset.


Local Open Scope Z.
  
Fixpoint set_list_union (S: gset Z) (L: list Z) : gset Z :=
  match L with
  | nil => S
  | h :: t => set_list_union (S ∪ {[ h ]}) t
  end.

Fixpoint Zset_inclusive_range (z: Z) (gap : nat) : gset Z :=
  match gap with
  | O => {[ z ]}
  | S n' => {[ z + S n']} ∪ (Zset_inclusive_range z n')
  end.

Definition Zset_exclusive_range (z: Z) (gap: nat) : gset Z :=
  Zset_inclusive_range z gap ∖  {[ z; z + gap ]}.

Definition Zlt_range (z1 z2: Z) : gset Z := 
  Zset_exclusive_range z1 (Z.to_nat (z2 - z1)).


Lemma in_inv {A: Type} :
  forall (l: list A) (a b: A) , In b (a :: l) ↔ b = a ∨ In b l.
Proof.
  intros l a b. split; intros H.
  + destruct l as [|c l]; inversion H; auto.
  + inversion H.
    - by left.
    - by right.
Qed.

Lemma in_inv_rev {A: Type} :
  forall (l: list A) (a b: A) , In b (l ++ [a]) ↔ In b l ∨ b = a.
Proof.
  intros l a b. split; intros H.
  + induction l as [|c l] using rev_ind.
    - inversion H; auto; by exfalso.
    - apply in_app_or in H. inversion H as [?|H'].
      * auto.
      * inversion H'; auto; by exfalso.
  + inversion H.
    - apply in_or_app. by left.
    - apply in_or_app. right. by left.
Qed.

Lemma list_split {A: Type} (l: list A) (n i: nat) :
  length l = S n → i ≤ n →
    ∃ (a: A) (l1 l2: list A), l = l1 ++ a :: l2 
               ∧ 
               length l1 = i ∧ length l2 = (n - i)%nat.
Proof.
  intros Hlength Hi.
  destruct l as [|a l]; first inversion Hlength.
  induction i as [|i].
  + exists a, nil, l.
    split; first auto.
    simpl in *; lia.
  + destruct IHi as [b IH]; first lia.
    destruct IH as [l1 IH]; destruct IH as [l2 IH].
    destruct IH as [Heq IH]; destruct IH as [Hlength1 Hlength2].
    destruct l2 as [|c l2]; first (inversion Hlength2; lia).

    exists c, (l1 ++ [b]), l2.
    rewrite app_ass app_length /=.
    split; first auto.
    simpl in *;lia.
Qed.

Lemma in_set_list_union (key: Z) (S: gset Z) (L: list Z) :
  key ∈ (set_list_union S L) ↔ key ∈ S ∨ key ∈ L.
Proof.
  split; revert S.
  + induction L as [|a L]; intros S Hin.
    - by left.
    - apply IHL in Hin. set_solver.
  + induction L as [|a L]; intros S Hin.
    - by destruct Hin as [Hin | Hin]; last inversion Hin.
    - apply IHL. set_solver.
Qed.

Lemma in_empty_set_list_union (key: Z) (L: list Z) :
  key ∈ (set_list_union ∅ L) ↔ key ∈ L.
Proof.
  split; intros Hin.
  + apply in_set_list_union in Hin.
    by destruct Hin; first exfalso.
  + apply in_set_list_union. by right. 
Qed.

Lemma no_dup_elem_unique {A: Type} (L1 L2 L1' L2': list A) elem elem1 elem2 :
  NoDup (L1 ++ elem1 :: elem :: L2) →
  L1 ++ elem1 :: elem :: L2 = L1' ++ elem2 :: elem :: L2' →
  elem1 = elem2.
Proof.
  rewrite NoDup_ListNoDup.
  revert L2 L1' L2'.
  induction L1 => //=.
  - intros L2 L1' L2' Hno_dup Heq.
    destruct L1' as [| a L1'].
    * rewrite //= in Heq; congruence. 
    * destruct L1' as [| b L1'].
      ** rewrite //= in Heq. assert (L2 = elem :: L2') by congruence.
        subst. exfalso.
        rewrite ?NoDup_cons_iff in Hno_dup *.
        destruct Hno_dup as [Hpred Hno_dup].
        destruct Hno_dup as [Hnp Hno_dup].
        destruct Hno_dup as [Hnp' Hno_dup].
        apply Hnp. by left.
      ** rewrite //= in Heq. assert (L2 = L1' ++ (elem2 :: elem :: L2')) by congruence.
        subst. 
        rewrite ?NoDup_cons_iff in Hno_dup *.
        destruct Hno_dup as [Hpred Hno_dup].
        destruct Hno_dup as [Hnp Hno_dup].
        exfalso. apply Hnp.
        apply in_or_app. right. econstructor; econstructor. auto.
  - intros L2 L1' L2' Hnd.
    destruct L1' as [| a' L1'].
    { rewrite //=.
      rewrite -NoDup_ListNoDup NoDup_cons in Hnd; destruct Hnd as [Ha Hnd].
      rewrite NoDup_app in Hnd; destruct Hnd as [Hl1 Hnd]; destruct Hnd as [Hx Hnd].
      intros Heq.
      cut (elem = elem1 ∨ In elem L1).
      { intros [Heqpred1|Hin].
        * exfalso.  subst.
          inversion Hnd as [|? ? Hpred Hnd']; subst.
          eapply Hpred. by left.
        * exfalso.  eapply Hx. 
          ** apply elem_of_list_In; eauto.
          ** right. by left.
      }
      destruct L1.
      * rewrite //= in Heq. inversion Heq; subst; auto.
      * right. inversion Heq; subst. by left.
    }
    inversion 1; subst. eapply IHL1; eauto.
    inversion Hnd; eauto.
Qed.

Lemma no_dup_inj_in_map {T1 T2: Type} (f: T1 → T2) (l: list T1) :
  (∀ x y, In x l → In y l → f x = f y → x = y) →
  NoDup l → NoDup (map f l).
Proof.
  intros Hinj.
  induction 1 as [|a l Hnin Hnd IH]; first constructor.
  rewrite //=. constructor.
  + intros Hin_map.
    rewrite elem_of_list_In in_map_iff in Hin_map.
    destruct Hin_map as [x Hin].
    destruct Hin as [Heq Hin].
    apply Hinj in Heq; subst.
    - destruct Hnin. rewrite elem_of_list_In //.
    - by right.
    - by left.
  + eapply IH. intros. eapply Hinj; last done. 
    all: by right.
Qed.

Lemma Zset_inclusive_range_spec z gap:
  ∀ z', z' ∈ (Zset_inclusive_range z gap) ↔ (z <= z' <= z + gap).
Proof.
  induction gap.
  + rewrite //= => z'. split.
    - intros ?%elem_of_singleton. subst. lia.
    - intros (?&?); assert (z = z') as -> by lia. rewrite elem_of_singleton //.
  + rewrite /Zset_inclusive_range -/Zset_inclusive_range => z'. split.
    - intros [Hspz%elem_of_singleton|Hrec]%elem_of_union.
      * lia.
      * destruct (IHgap z') as (Himp&?). specialize (Himp Hrec). lia.
    - intros (?&Hle).
      apply Zle_lt_or_eq in Hle as [Hlt|?].
      * apply elem_of_union_r. eapply IHgap. lia.
      * apply elem_of_union_l. rewrite elem_of_singleton //.
Qed.

Lemma Zset_exclusive_range_spec z gap:
  ∀ z', z' ∈ (Zset_exclusive_range z gap) ↔ (z < z' < z + gap).
Proof.
  intros z'. split.
  - rewrite /Zset_exclusive_range.
    intros (Hincl&Hneq)%elem_of_difference.
    apply Zset_inclusive_range_spec in Hincl.
    assert (z' ≠ z ∧ z' ≠ z + gap) by set_solver.
    lia.
  - rewrite /Zset_exclusive_range. 
    intros Hrange.
    apply elem_of_difference; split.
    * apply Zset_inclusive_range_spec; lia.
    * assert (z' ≠ z ∧ z' ≠ z + gap) by lia.
      set_solver.
Qed.

Lemma Zlt_range_spec z1 z2:
  ∀ z', z' ∈ (Zlt_range z1 z2) ↔ (z1 < z' < z2).
Proof.
  intros z'.
  rewrite /Zlt_range Zset_exclusive_range_spec; lia.
Qed.

Lemma gset_union_diff (z: Z) (S Sminus: gset Z) :
  z ∈ S →
  z ∉ Sminus →
  S ∖ Sminus = (S ∖ (Sminus ∪ {[ z ]})) ∪ {[ z ]}.
Proof.
  intros Hin Hnin.
  rewrite -leibniz_equiv_iff.
  intros x. split.
  + intros Hin_diff. apply elem_of_union.
    destruct (Ztrichotomy_inf x z) as [[Hlt|Heq]|Hgt].
    - left. assert (x ≠ z) by lia. set_solver.
    - right. rewrite elem_of_singleton //.
    - left. assert (x ≠ z) by lia. set_solver.
  + intros [Hin_diff|Hin_singleton]%elem_of_union; set_solver.
Qed.

Section gset_extra.
  Context `{Countable K}.
  Implicit Types X Y Z : gset K.
  Lemma gset_local_update_union X Y W : (X,Y) ~l~> (X ∪ W,Y ∪ W).
  Proof.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite gset_op. set_solver.
  Qed.
End gset_extra.