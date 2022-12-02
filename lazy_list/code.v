From iris.heap_lang Require Export notation spin_lock.

From SkipList.lib Require Import node_rep.


Local Open Scope Z.

Module Type LAZY_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

Module LazyList (Params: LAZY_LIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep := (INT_MAX, dummy_null, dummy_null, None, dummy_lock, dummy_null).  

  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
        ref (#INT_MIN, #dummy_null, "t", NONEV, newlock #(), #dummy_null).

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
        if: "k" = nodeKey "succ"
        then release (nodeLock "pred")
        else let: "np" := nodeNext "pred" in
             let: "next" := ref !"np" in
               "np" <- ("k", #dummy_null, "next", NONEV, newlock #(), #dummy_null);;
               release (nodeLock "pred").

End LazyList.
