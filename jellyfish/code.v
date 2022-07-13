From iris.heap_lang Require Export notation spin_lock.

From SkipList.lib Require Import node_rep.


Local Open Scope Z.

Module Type SKIP_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter MAX_HEIGHT : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
  Parameter (HMAX_HEIGHT: 0 ≤ MAX_HEIGHT).
End SKIP_LIST_PARAMS.

Module SkipList (Params: SKIP_LIST_PARAMS).
  Import Params.
  
  Definition tail : node_rep := (INT_MAX, dummy_null, dummy_null, None, dummy_lock).

  (* Skip list constructor *)  
  Definition new : val := 
    λ: "_", 
      let: "np" := ref (rep_to_node tail) in
      let: "next" := AllocN #(MAX_HEIGHT + 1) "np" in
        ref (#INT_MIN, #dummy_null, "next", NONEV, newlock #()).

  (* Find function *)
  Definition find : val := 
    rec: "find" "pred" "k" "lvl" :=
      let: "np" := nodeNext "pred" in
      let: "succ" := ! !("np" +ₗ "lvl") in
      let: "ck" := nodeKey "succ" in
        if: "k" ≤ "ck"
        then ("pred", "succ")
        else "find" "succ" "k" "lvl".
  
  Definition findLock : val := 
    rec: "find" "head" "k" "lvl" :=
      let: "pair" := find "head" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
        acquire (nodeLock "pred");;
        let: "np" := nodeNext "pred" in
        let: "next" := ! !("np" +ₗ "lvl") in
        let: "nk" := nodeKey "next" in
        let: "ck" := nodeKey "curr" in
          if: "nk" = "ck" 
          then "pair"
          else
            release (nodeLock "pred");;
            "find" "pred" "k" "lvl".

  (* Skip list lookup *)
  Definition findPred : val := 
    rec: "find" "pred" "k" "lvl" := 
      let: "pair" := find "pred" "k" "lvl" in
        if: "lvl" = #0
        then "pair"
        else 
          let: "pred" := Fst "pair" in
            "find" "pred" "k" ("lvl" - #1).

  Definition get : val :=
    λ: "head" "k", 
      let: "np" := !"head" in
      let: "pair" := findPred "np" "k" #MAX_HEIGHT in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        if: "k" = "ck"
        then NONEV
        else 
          let: "val" := nodeVal "curr" in
            SOME (Fst "val").

  (* Link node in lazy list *)
  Definition createAndLink : val := 
    λ: "pred" "k" "v" "t" "h",
      let: "np" := nodeNext "pred" in
      let: "succ" := !"np" in
      let: "next" := AllocN ("h" + #1) #() in
      let: "val" := ref ("t", "v", #dummy_null) in
      let: "node" := ref ("k", "val", #dummy_null, "next", NONEV, newlock #()) in
        acquire (nodeLock !"node");;
        "next" <- "succ";;
        "np" <- "node";;
        "node".

  Definition link : val := 
    λ: "pred" "lvl" "node",
      let: "np" := nodeNext "pred" in
      let: "succ" := !("np" +ₗ "lvl") in
      let: "next" := nodeNext !"node" in
        ("next" +ₗ "lvl") <- "succ";;
        ("np" +ₗ "lvl") <- "node".

  (* Lazy list insertion *)
  Definition update : val := 
    λ: "head" "k" "h",
      let: "pair" := findLock "head" "k" #0 in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
      let: "ck" := nodeKey "curr" in
        if: "k" = "ck"
        then 
          let: "vp" := nodeVal "curr" in
          let: "val" := !"vp" in
          let: "ts" := valTs "val" in
            if: "t" < "ts" 
            then
              release (nodeLock "pred");;
              NONEV
            else
              let: "new" := ("t", "v", ref "val") in
                "vp" <- "new";;
                release (nodeLock "pred");;
                NONEV
        else 
          let: "node" := createAndLink "pred" "k" "v" "t" "h" in
            release (nodeLock "pred");;
            SOME "node".

  Definition insert : val := 
    λ: "head" "lvl" "node",
      let: "k" := nodeKey !"node" in
      let: "pair" := findLock "head" "k" "lvl" in
      let: "pred" := Fst "pair" in
        link "pred" "lvl" "node";;
        release (nodeLock "pred").

  (* Skip list insertion *)
  Definition topLevel : val := 
    rec: "loop" "head" "k" "h" "lvl" :=
      let: "pair" := find "head" "k" "lvl" in
      let: "pred" := Fst "pair" in
        if: "h" = "lvl"
        then "pred"
        else "loop" "pred" "k" "h" ("lvl" - #1).
      
  Definition putAll : val := 
    rec: "put" "head" "k" "v" "t" "h" "lvl" := 
      let: "pair" := find "head" "k" "lvl" in
      let: "pred" := Fst "pair" in
        if: "lvl" = #0
        then update "pred" "k" "v" "t" "h"
        else
          let: "onode" := "put" "pred" "k" "v" "t" "h" ("lvl" - #1) in
            match: "onode" with
              NONE => NONEV
            | SOME "node" =>
              insert "pred" "lvl" "node";;
              SOME "node"
            end.

  Definition put : val := 
    λ: "head" "k" "v" "t" "h",
      let: "np" := !"head" in
      let: "pred" := topLevel "np" "k" "h" #MAX_HEIGHT in
      let: "onode" := putAll "pred" "k" "v" "t" "h" "h" in
        match: "onode" with
          NONE => #()
        | SOME "node" => release (nodeLock !"node")
        end.

End SkipList.
