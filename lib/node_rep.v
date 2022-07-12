From iris.heap_lang Require Import notation.

Local Open Scope Z.

Definition val_rep : Type := Z * val * loc.

Definition val_ts (v: val_rep) : Z := v.1.1.
Definition val_v (v: val_rep) : val := v.1.2.
Definition val_next (v: val_rep) : loc := v.2.

Definition valTs : val := λ: "l", Fst (Fst "l").
Definition valV : val := λ: "l", Snd (Fst "l").
Definition valNext : val := λ: "l", Snd "l".

Definition rep_to_val (v: val_rep) : val := 
  (#(val_ts v), val_v v, #(val_next v)).

Definition node_rep : Type := Z * loc * loc * option loc * val.

Definition node_key (n: node_rep) : Z := n.1.1.1.1.
Definition node_val (n: node_rep) : loc := n.1.1.1.2.
Definition node_next (n: node_rep) : loc := n.1.1.2.
Definition node_down (n: node_rep) : option loc := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition nodeKey : val := λ: "l", Fst (Fst (Fst (Fst "l"))).
Definition nodeVal : val := λ: "l", Snd (Fst (Fst (Fst "l"))).
Definition nodeNext : val := λ: "l", Snd (Fst (Fst "l")).
Definition nodeDown : val := λ: "l", Snd (Fst "l").
Definition nodeLock : val := λ: "l", Snd "l".

Definition oloc_to_val (ol: option loc) : val := 
  match ol with
  | None => NONEV
  | Some l => SOMEV #l
  end.

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), #(node_val n), #(node_next n), oloc_to_val (node_down n), (node_lock n)).

Definition dummy_null : loc := {|loc_car := 0|}.
Definition dummy_lock : val := #().


Lemma fold_rep_to_val (v: val_rep) :
  ((#(val_ts v), val_v v, #(val_next v)))%V =
  rep_to_val v.
Proof. done. Qed.

Lemma fold_rep_to_node (n: node_rep) :
  ((#(node_key n), #(node_val n), #(node_next n), oloc_to_val (node_down n), (node_lock n)))%V =
  rep_to_node n.
Proof. done. Qed.

Lemma rep_to_val_inj rep rep' :
  rep_to_val rep = rep_to_val rep' →
  rep = rep'.
Proof.
  destruct rep as ((?&?)&?).
  destruct rep' as ((?&?)&?).
  rewrite /rep_to_val/val_ts/val_v/val_next/=.
  intros; congruence.
Qed.

Lemma rep_to_node_inj rep rep':
  rep_to_node rep = rep_to_node rep' →
  rep = rep'.
Proof.
  destruct rep as ((((?&v)&?)&down)&?). 
  destruct rep' as ((((?&v')&?)&down')&?).
  rewrite /rep_to_node/node_key/node_val/node_next/node_down/node_lock//=.
  destruct down; destruct down'.
  all: inversion 1; congruence.
Qed.