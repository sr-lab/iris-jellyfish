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

  Definition tail : node_rep := (INT_MAX, dummy_null, dummy_null, None, dummy_lock, dummy_null).

  Definition initLevels : val := 
    rec: "init" "head" "l" :=
      let: "h" := ref "head" in
        if: "l" = #MAX_HEIGHT then "h"
        else let: "t" := ref (rep_to_node tail) in
             let: "head" := (#INT_MIN, #dummy_null, "t", SOME "h", newlock #(), #dummy_null) in
               "init" "head" ("l" + #1).
  
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      let: "head" := (#INT_MIN, #dummy_null, "t", NONEV, newlock #(), #dummy_null) in
        initLevels "head" #0.

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

  Definition findAll : val := 
    rec: "find" "pred" "k" := 
      let: "pair" := find "pred" "k" in
      let: "pred" := Fst "pair" in
        match: nodeDown "pred" with
          NONE => "pair"
        | SOME "n" => "find" !"n" "k"
        end.

  Definition contains : val := 
    λ: "p" "k", 
      let: "pair" := findAll !"p" "k" in
      let: "succ" := Snd "pair" in
        "k" = nodeKey "succ".

  Definition createAndLink : val := 
    λ: "pred" "k" "odown",
      let: "np" := nodeNext "pred" in
      let: "next" := ref !"np" in
      let: "node" := ("k", #dummy_null, "next", "odown", newlock #(), #dummy_null) in
        "np" <- "node";;
        "node".

  Definition insert : val := 
    λ: "head" "down",
      let: "k" := nodeKey "down" in
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" in
      let: "d" := ref "down" in
      let: "node" := createAndLink "pred" "k" (SOME "d") in
        release "lock";;
        "node".

  Definition tryInsert : val := 
    λ: "head" "k",
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
      let: "lock" := nodeLock "pred" in
        if: "k" = nodeKey "succ"
        then release "lock";;
             NONEV
        else let: "node" := createAndLink "pred" "k" NONEV in
               release "lock";;
               SOME "node".

  Definition findLevel : val := 
    rec: "find" "pred" "k" "lvl" "h" :=
      let: "pair" := find "pred" "k" in
      let: "pred" := Fst "pair" in
        if: "lvl" = "h" then "pred"
        else match: nodeDown "pred" with
               NONE => #()
             | SOME "d" => "find" !"d" "k" ("lvl" - #1) "h"
             end.
      
  Definition insertAll : val := 
    rec: "insert" "curr" "k" := 
      match: nodeDown "curr" with
        NONE => tryInsert "curr" "k"
      | SOME "d" => let: "pair" := find !"d" "k" in
                    let: "pred" := Fst "pair" in
                    let: "opt" := "insert" "pred" "k" in
                      match: "opt" with
                        NONE => NONEV
                      | SOME "down" => let: "node" := insert "curr" "down" in
                                         SOME "node"
                      end
      end.

  Definition addH : val := 
    λ: "p" "k" "h",
      let: "pred" := findLevel !"p" "k" #MAX_HEIGHT "h" in
        insertAll "pred" "k".

  (* HeapLang does not support randomness... *)
  Definition randomLevel : val :=
    λ: "_", #0.

  Definition add : val :=
    λ: "p" "k",
      let: "h" := randomLevel #() in
      let: "opt" := addH "p" "k" "h" in #().

End SkipList.
