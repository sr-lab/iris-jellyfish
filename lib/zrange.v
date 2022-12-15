From iris.algebra Require Import gset.


Section zrange.
  Local Open Scope Z.

  Fixpoint zrange_gap (l: Z) (gap : nat) : gset Z :=
    match gap with
    | O => ∅
    | S n => 
      match n with
      | O => ∅
      | S _ => {[l + n]} ∪ (zrange_gap l n)
      end
    end.
  Lemma zrange_gap_spec m l gap:
    m ∈ zrange_gap l gap ↔ l < m < l + gap.
  Proof.
    destruct gap as [|gap]. { split; intros; last lia; done. }
    induction gap as [|gap IH]. { split; intros; last lia; done. }
    rewrite elem_of_union; split.
    + intros [Hsing|Hrange].
      - rewrite elem_of_singleton in Hsing; lia.
      - rewrite IH in Hrange; lia.
    + replace (l + S (S gap)) with (Z.succ (l + S gap)) by lia.
      intros (?&Hle); apply Zlt_succ_le, Zle_lt_or_eq in Hle as [?|?].
      - right; rewrite IH; lia.
      - left; rewrite elem_of_singleton //.
  Qed.

  Definition zrange (l r: Z) : gset Z := 
    zrange_gap l (Z.to_nat (r - l)).
  Lemma zrange_spec m l r:
    m ∈ zrange l r ↔ l < m < r.
  Proof. rewrite /zrange zrange_gap_spec; lia. Qed.
  Lemma zrange_disj S l r:
    S ## zrange l r ↔ ∀ m, l < m < r → m ∉ S.
  Proof. pose proof zrange_spec; set_solver. Qed.
  Lemma zrange_disj_l l r:
    {[l]} ## zrange l r.
  Proof. intros ?; rewrite zrange_spec elem_of_singleton; lia. Qed.
  Lemma zrange_disj_r l r:
    zrange l r ## {[r]}.
  Proof. intros ?; rewrite zrange_spec elem_of_singleton; lia. Qed.
  Lemma zrange_disj_m m l r:
    zrange l m ## zrange m r.
  Proof. intros ?; do 2 rewrite zrange_spec; lia. Qed.
  Lemma zrange_split m l r:
    l < m < r → zrange l r = zrange l m ∪ {[m]} ∪ zrange m r.
  Proof.
    intros Hm; rewrite set_eq; intros m'; split.
    + intros Hm'%zrange_spec.
      destruct (Ztrichotomy_inf m' m) as [[Hlt|<-]|Hgt].
      - apply elem_of_union_l, elem_of_union_l, zrange_spec; lia.
      - by apply elem_of_union_l, elem_of_union_r, elem_of_singleton.
      - apply elem_of_union_r, zrange_spec; lia.
    + rewrite ?elem_of_union elem_of_singleton ?zrange_spec; intros [[Hlt|Heq]|Hgt]; lia.
  Qed.
End zrange.

Section ZRange.
  Local Open Scope Z.

  Definition ZRange (l r: Z) : gset_disj Z := 
    if decide(l < r) then GSet (zrange l r) else GSetBot.
  Lemma ZRange_disj S l r:
    ✓ (GSet S ⋅ ZRange l r) ↔ S ## zrange l r ∧ l < r.
  Proof. rewrite /ZRange; case_decide; first set_solver; by split; last lia. Qed.
  Lemma ZRange_split m l r:
    l < m < r → ZRange l r = ZRange l m ⋅ GSet {[m]} ⋅ ZRange m r.
  Proof.
    intros ?; rewrite /ZRange; do 3 (case_decide; last lia).
    rewrite (zrange_split m) // gset_disj_union; last apply zrange_disj_r.
    rewrite gset_disj_union // disjoint_union_l.
    split; first apply zrange_disj_m; apply zrange_disj_l.
  Qed.
End ZRange.