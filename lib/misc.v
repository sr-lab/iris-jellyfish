From stdpp Require Export gmap.

From iris.heap_lang Require Export notation.


Definition oloc_to_val (ol: option loc) : val := 
  match ol with
  | None => NONEV
  | Some l => SOMEV #l
  end.

Local Open Scope Z.
Definition node_rep : Type := Z * option loc * val.
Definition node_key (n: node_rep) : Z := n.1.1.
Definition node_next (n: node_rep) : option loc := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition node_lt (x y: node_rep) : Prop := 
  node_key x < node_key y.

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), oloc_to_val (node_next n), (node_lock n)).

Definition key_equiv (S: gset node_rep) (S_keys: gset Z) :=
  Permutation (elements S_keys) (map node_key (elements S)).