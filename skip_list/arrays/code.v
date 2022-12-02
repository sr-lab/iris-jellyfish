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

  Definition new : val := 
    λ: "_", 
      let: "np" := ref (rep_to_node tail) in
      let: "next" := AllocN #(MAX_HEIGHT + 1) "np" in
        ref (#INT_MIN, #dummy_null, "next", NONEV, newlock #(), #dummy_null).

  Definition find : val := 
    rec: "find" "pred" "k" "lvl" :=
      let: "succ" := ! !(nodeNext "pred" +ₗ "lvl") in
        if: "k" ≤ nodeKey "succ" then ("pred", "succ")
        else "find" "succ" "k" "lvl".
  
  Definition findLock : val := 
    rec: "find" "pred" "k" "lvl" :=
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" in
        acquire "lock";;
        let: "succ" := ! !(nodeNext "pred" +ₗ "lvl") in
          if: "k" ≤ nodeKey "succ" then ("pred", "succ")
          else release "lock";;
               "find" "succ" "k" "lvl".

  Definition findAll : val := 
    rec: "find" "pred" "k" "lvl" "h" := 
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
        if: "lvl" = "h" then "pair"
        else "find" "pred" "k" ("lvl" - #1) "h".

  Definition contains : val := 
    λ: "p" "k", 
      let: "pair" := findAll !"p" "k" #MAX_HEIGHT #0 in
      let: "succ" := Snd "pair" in
        "k" = nodeKey "succ".
  
  Definition link : val := 
    λ: "pred" "lvl" "n",
      let: "new" := !"n" in
        nodeNext "new" +ₗ "lvl" <- !(nodeNext "pred" +ₗ "lvl") ;;
        nodeNext "pred" +ₗ "lvl" <- "n".

  Definition insert : val := 
    λ: "pred" "lvl" "n",
      let: "k" := nodeKey !"n" in
      let: "pair" := findLock "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" in
        link "pred" "lvl" "n";;
        release "lock".

  Definition createAndLink : val := 
    λ: "pred" "k" "h",
      let: "next" := AllocN ("h" + #1) #() in
      let: "n" := ref ("k", #dummy_null, "next", NONEV, newlock #(), #dummy_null) in
        acquire (nodeLock !"n");;
        link "pred" #0 "n";;
        "n".

  Definition tryInsert : val := 
    λ: "pred" "k" "h",
      let: "pair" := findLock "pred" "k" #0 in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
      let: "lock" := nodeLock "pred" in
        if: "k" = nodeKey "succ"
        then release "lock";;
             NONEV
        else let: "n" := createAndLink "pred" "k" "h" in
               release "lock";;
               SOME "n".

  Definition insertAll : val := 
    rec: "insert" "curr" "k" "h" "lvl" := 
      if: "lvl" = #0 then tryInsert "curr" "k" "h"
      else let: "pair" := find "curr" "k" ("lvl" - #1) in
           let: "pred" := Fst "pair" in
           let: "opt" := "insert" "pred" "k" "h" ("lvl" - #1) in
             match: "opt" with
               NONE => NONEV
             | SOME "n" => insert "curr" "lvl" "n";;
                           SOME "n"
             end.

  Definition addH : val := 
    λ: "p" "k" "h",
      let: "pair" := findAll !"p" "k" #MAX_HEIGHT "h" in
      let: "pred" := Fst "pair" in
      let: "opt" := insertAll "pred" "k" "h" "h" in
        match: "opt" with
          NONE => "opt"
        | SOME "n" => release (nodeLock !"n");;
                      "opt"
        end.

  (* HeapLang does not support randomness... *)
  Definition randomLevel : val :=
    λ: "_", #0.

  Definition add : val :=
    λ: "p" "k",
      let: "h" := randomLevel #() in
      let: "opt" := addH "p" "k" "h" in #().

End SkipList.
