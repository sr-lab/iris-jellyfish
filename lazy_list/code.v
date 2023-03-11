From iris.heap_lang Require Import notation.

From SkipList.atomic Require Import proofmode lock.


Section node_rep.
  Definition node_rep : Type := Z * loc * loc.
  Definition dummy_null : loc := {|loc_car := 0|}.

  Definition node_key (n: node_rep) : Z := n.1.1.
  Definition node_next (n: node_rep) : loc := n.1.2.
  Definition node_lock (n: node_rep) : loc := n.2.

  Definition nodeKey : val := λ: "l", Fst (Fst "l").
  Definition nodeNext : val := λ: "l", Snd (Fst "l").
  Definition nodeLock : val := λ: "l", Snd "l".

  Definition rep_to_node (n: node_rep) : val :=
    (#(node_key n), #(node_next n), #(node_lock n)).
  Lemma fold_rep_to_node (n: node_rep) :
    ((#(node_key n), #(node_next n), #(node_lock n)))%V = rep_to_node n.
  Proof. done. Qed.
  Lemma rep_to_node_inj rep rep':
    rep_to_node rep = rep_to_node rep' → rep = rep'.
  Proof.
    destruct rep as ((?&?)&?); destruct rep' as ((?&?)&?). 
    rewrite /rep_to_node/node_key/node_next/node_lock/=; congruence.
  Qed.
End node_rep.

Module Type LAZY_LIST_PARAMS.
  Local Open Scope Z.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

Module LazyList (Params: LAZY_LIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep := (INT_MAX, dummy_null, dummy_null).

  Definition new : val := 
    λ: "_", 
      let: "n" := ref (rep_to_node tail) in
      let: "l" := ref #false in
        ref (#INT_MIN, "n", "l").

  Definition find : val := 
    rec: "find" "pred" "k" :=
      let: "succ" := !(nodeNext "pred") in
        if: "k" ≤ nodeKey "succ" then ("pred", "succ")
        else "find" "succ" "k".
  
  Definition findLock : val := 
    rec: "find" "pred" "k" :=
      let: "pair" := find "pred" "k" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" in
        acquire "lock";;
        let: "succ" := !(nodeNext "pred") in
          if: "k" ≤ nodeKey "succ" then ("pred", "succ")
          else release "lock";;
               "find" "succ" "k".

  Definition contains : val := 
    λ: "p" "k",
      let: "pair" := find !"p" "k" in
      let: "succ" := Snd "pair" in
        "k" = nodeKey "succ".
  
  Definition add : val := 
    λ: "p" "k",
      let: "pair" := findLock !"p" "k" in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
      let: "lock" := nodeLock "pred" in
        if: "k" = nodeKey "succ"
        then release "lock"
        else let: "np" := nodeNext "pred" in
             let: "n" := ref !"np" in
             let: "l" := ref #false in
               "np" <- ("k", "n", "l");;
               release "lock".

End LazyList.
