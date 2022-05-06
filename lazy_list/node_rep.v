From iris.heap_lang Require Import notation.

Local Open Scope Z.

Definition node_rep : Type := Z * option loc * val.
Definition node_key (n: node_rep) : Z := n.1.1.
Definition node_next (n: node_rep) : option loc := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition oloc_to_val (ol: option loc) : val := 
  match ol with
  | None => NONEV
  | Some l => SOMEV #l
  end.

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), oloc_to_val (node_next n), (node_lock n)).


Lemma fold_rep_to_node (n: node_rep) :
  ((#(node_key n), oloc_to_val (node_next n), (node_lock n)))%V =
  rep_to_node n.
Proof. done. Qed.

Lemma rep_to_node_inj rep rep':
  rep_to_node rep = rep_to_node rep' →
  rep = rep'.
Proof.
  destruct rep as ((?&o)&?). 
  destruct rep' as ((?&o')&?). 
  rewrite /rep_to_node/node_key/node_lock/node_next//=.
  destruct o; destruct o'; inversion 1; congruence.
Qed.