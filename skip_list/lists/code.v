From iris.heap_lang Require Export notation spin_lock.

From SkipList.lib Require Import node_rep.


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
  Definition newLoop : val := 
    rec: "loop" "head" "l" :=
      let: "h" := ref "head" in
        if: "l" = #MAX_HEIGHT
        then "h"
        else
          let: "t" := ref (rep_to_node tail) in
          let: "head" := (#INT_MIN, "t", SOME "h", newlock #()) in
            "loop" "head" ("l" + #1).
  
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      let: "head" := (#INT_MIN, "t", NONEV, newlock #()) in
        newLoop "head" #0.

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

  (* Skip list lookup *)
  Definition findPred : val := 
    rec: "find" "head" "k" := 
      let: "pair" := find "head" "k" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
        match: nodeDown "pred" with
          NONE => "pair"
        | SOME "np" => 
          let: "pred" := !"np" in
            "find" "pred" "k"
        end.

  Definition contains : val := 
    λ: "head" "k", 
      let: "np" := !"head" in
      let: "pair" := findPred "np" "k" in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        "k" = "ck".

  (* Link node in lazy list *)
  Definition link : val := 
    λ: "pred" "k" "odown",
      let: "np" := nodeNext "pred" in
      let: "succ" := !"np" in
      let: "next" := ref "succ" in
      let: "node" := ("k", "next", "odown", newlock #()) in
        "np" <- "node";;
        release (nodeLock "pred");;
        "node".

  (* Lazy list insertion *)
  Definition tryInsert : val := 
    λ: "head" "k",
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
      let: "ck" := (nodeKey "curr") in
        if: "k" = "ck"
        then
          release (nodeLock "pred");;
          NONEV
        else
          let: "node" := link "pred" "k" NONEV in
            SOME "node".

  Definition insert : val := 
    λ: "head" "k" "down",
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      let: "d" := ref "down" in
        link "pred" "k" (SOME "d").

  (* Skip list insertion *)
  Definition topLevel : val := 
    rec: "loop" "head" "k" "h" "l" :=
      let: "pair" := find "head" "k" in
      let: "pred" := Fst "pair" in
        if: "h" = "l"
        then "pred"
        else
          match: nodeDown "pred" with
            NONE => #()
          | SOME "np" => 
            let: "pred" := !"np" in
              "loop" "pred" "k" "h" ("l" - #1)
          end.
      
  Definition addAll : val := 
    rec: "add" "head" "k" := 
      let: "pair" := find "head" "k" in
      let: "pred" := Fst "pair" in
        match: nodeDown "pred" with
          NONE => tryInsert "pred" "k"
        | SOME "np" => 
          let: "down" := !"np" in
          let: "onode" := "add" "down" "k" in
          match: "onode" with 
            NONE => NONEV
          | SOME "node" => 
            let: "node" := insert "pred" "k" "node" in
              SOME "node"
          end
        end.

  Definition add : val := 
    λ: "head" "k" "h",
      let: "np" := !"head" in
      let: "pred" := topLevel "np" "k" "h" #MAX_HEIGHT in
      let: "onode" := addAll "pred" "k" in
        match: "onode" with
          NONE => #false
        | SOME "node" => #true
        end.

End SkipList.
