From SkipList.lib Require Import lock node_rep.


Local Open Scope Z.

Module Type SKIP_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter MAX_HEIGHT : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End SKIP_LIST_PARAMS.

Module SkipList (Params: SKIP_LIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep := (INT_MAX, dummy_null, None, dummy_lock).

  (* Skip list constructor *)  
  Definition new : val := 
    λ: "_", 
      let: "np" := ref (rep_to_node tail) in
      let: "next" := AllocN #MAX_HEIGHT "np" in
        ref (#INT_MIN, "next", NONEV, newlock #()).

  (* Find function *)
  Definition find : val := 
    rec: "find" "pred" "k" "i" :=
      let: "np" := nodeNext "pred" in
      let: "succ" := ! !("np" +ₗ "i") in
      let: "ck" := nodeKey "succ" in
        if: "k" ≤ "ck"
        then ("pred", "succ")
        else "find" "succ" "k" "i".
  
  Definition findLock : val := 
    rec: "find" "head" "k" "i" :=
      let: "pair" := find "head" "k" "i" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
        acquire (nodeLock "pred");;
        let: "np" := nodeNext "pred" in
        let: "next" := ! !("np" +ₗ "i") in
        let: "nk" := nodeKey "next" in
        let: "ck" := nodeKey "curr" in
          if: "nk" = "ck" 
          then "pair"
          else
            release (nodeLock "pred");;
            "find" "pred" "k" "i".

  (* Skip list lookup *)
  Definition findPred : val := 
    rec: "find" "pred" "k" "i" := 
      let: "pair" := find "pred" "k" "i" in
        if: "i" = #0
        then "pair"
        else 
          let: "pred" := Fst "pair" in
            "find" "pred" "k" ("i" - #1).

  Definition contains : val := 
    λ: "head" "k", 
      let: "np" := !"head" in
      let: "pair" := findPred "np" "k" #MAX_HEIGHT in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        "k" = "ck".

  (* Link node in lazy list *)
  Definition createAndLink : val := 
    λ: "pred" "k" "h",
      let: "np" := nodeNext "pred" in
      let: "succ" := !"np" in
      let: "next" := AllocN "h" #() in
      let: "node" := ref ("k", "next", NONEV, newlock #()) in
        "next" <- "succ";;
        "np" <- "node";;
        "node".

  Definition link : val := 
    λ: "pred" "i" "node",
      let: "np" := nodeNext "pred" in
      let: "succ" := !("np" +ₗ "i") in
      let: "next" := nodeNext !"node" in
        ("next" +ₗ "i") <- "succ";;
        ("np" +ₗ "i") <- "node";;
        release (nodeLock "pred").

  (* Lazy list insertion *)
  Definition tryInsert : val := 
    λ: "head" "k" "h",
      let: "pair" := findLock "head" "k" #0 in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        if: "k" = "ck"
        then 
          release (nodeLock "pred");;
          NONEV
        else 
          let: "node" := createAndLink "pred" "k" "h" in
            release (nodeLock "pred");;
            SOME "node".

  Definition insert : val := 
    λ: "head" "i" "node",
      let: "k" := nodeKey !"node" in
      let: "pair" := findLock "head" "k" "i" in
      let: "pred" := Fst "pair" in
        link "pred" "i" "node";;
        release (nodeLock "pred").

  (* Skip list insertion *)
  Definition topLevel : val := 
    rec: "loop" "head" "k" "h" "i" :=
      let: "pair" := find "head" "k" "i" in
      let: "pred" := Fst "pair" in
        if: "h" = "i"
        then "pred"
        else "loop" "pred" "k" "h" ("i" - #1).
      
  Definition addAll : val := 
    rec: "add" "head" "k" "h" "i" := 
      let: "pair" := find "head" "k" "i" in
      let: "pred" := Fst "pair" in
        if: "i" = #0
        then tryInsert "pred" "k" "h"
        else
          let: "onode" := "add" "pred" "k" "h" ("i" - #1) in
            match: "onode" with
              NONE => NONEV
            | SOME "node" =>
              insert "pred" "i" "node";;
              SOME "node"
            end.

  Definition add : val := 
    λ: "head" "k" "h",
      let: "np" := !"head" in
      let: "pred" := topLevel "np" "k" "h" #MAX_HEIGHT in
      let: "onode" := addAll "pred" "k" "h" "h" in
        match: "onode" with
          NONE => #false
        | SOME "node" => #true
        end.

End SkipList.
