From SkipList.lib Require Import lock node_rep.


Local Open Scope Z.

Module Type LAZY_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

Module LazyList (Params: LAZY_LIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep := (INT_MAX, dummy_null, None, dummy_lock).  

  (* Lazy list constructor *)
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      ref (#INT_MIN, "t", NONEV, newlock #()).

  (* Find function *)
  Definition find : val := 
    rec: "find" "pred" "k" :=
      let: "curr" := !(nodeNext "pred") in
      let: "ck" := nodeKey "curr" in
        if: "k" ≤ "ck"
        then ("pred", "curr")
        else "find" "curr" "k".
  
  Definition findLock : val := 
    rec: "find" "head" "k" :=
      let: "pair" := find "head" "k" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
        acquire (nodeLock "pred");;
        let: "next" := !(nodeNext "pred") in
        let: "nk" := nodeKey "next" in
        let: "ck" := nodeKey "curr" in
          if: "nk" = "ck" 
          then "pair"
          else
            release (nodeLock "pred");;
            "find" "pred" "k".

  (* Lazy list lookup *)
  Definition contains : val := 
    λ: "head" "k",
      let: "np" := !"head" in
      let: "pair" := find "np" "k" in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        ("k" = "ck").
  
  (* Lazy list insertion *)
  Definition add : val := 
    λ: "head" "k",
      let: "np" := !"head" in
      let: "pair" := findLock "np" "k" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        if: "k" = "ck"
        then
          release (nodeLock "pred");;
          #false
        else
          let: "np" := nodeNext "pred" in
          let: "succ" := !"np" in
          let: "next" := ref "succ" in
          let: "node" := ("k", "next", NONEV, newlock #()) in
            "np" <- "node";;
            release (nodeLock "pred");;
            #true.

End LazyList.
