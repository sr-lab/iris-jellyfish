From iris.heap_lang Require Import notation.

Local Open Scope Z.

Definition node_rep : Type := Z * loc * option loc * val.

Definition node_key (n: node_rep) : Z := n.1.1.1.
Definition node_next (n: node_rep) : loc := n.1.1.2.
Definition node_down (n: node_rep) : option loc := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition nodeKey : val := λ: "l", Fst (Fst (Fst "l")).
Definition nodeNext : val := λ: "l", Snd (Fst (Fst "l")).
Definition nodeDown : val := λ: "l", Snd (Fst "l").
Definition nodeLock : val := λ: "l", Snd "l".

Definition dummy_null : loc := {|loc_car := 0|}.
Definition dummy_lock : val := #().

Definition oloc_to_val (ol: option loc) : val := 
  match ol with
  | None => NONEV
  | Some l => SOMEV #l
  end.

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), #(node_next n), oloc_to_val (node_down n), (node_lock n)).


Lemma fold_rep_to_node (n: node_rep) :
  ((#(node_key n), #(node_next n), oloc_to_val (node_down n), (node_lock n)))%V =
  rep_to_node n.
Proof. done. Qed.

Lemma rep_to_node_inj rep rep':
  rep_to_node rep = rep_to_node rep' →
  rep = rep'.
Proof.
  destruct rep as (((?&?)&down)&?). 
  destruct rep' as (((?&?)&down')&?).
  rewrite /rep_to_node/node_key/node_next/node_down/node_lock//=.
  destruct down; destruct down'.
  all: inversion 1; congruence.
Qed.