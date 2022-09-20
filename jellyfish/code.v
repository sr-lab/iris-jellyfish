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

  Definition initLocks : val := 
    rec: "init" "locks" "lvl" :=
      if: "lvl" = #(MAX_HEIGHT + 1) then #()
      else "locks" +ₗ "lvl" <- newlock #();;
           "init" "locks" ("lvl" + #1).

  Definition new : val := 
    λ: "_", 
      let: "next" := AllocN #(MAX_HEIGHT + 1) (ref (rep_to_node tail)) in
      let: "locks" := AllocN #(MAX_HEIGHT + 1) #() in
        initLocks "locks" #0;;
        ref (#INT_MIN, #dummy_null, "next", NONEV, dummy_lock, "locks").

  Definition find : val := 
    rec: "find" "pred" "k" "lvl" :=
      let: "succ" := ! !(nodeNext "pred" +ₗ "lvl") in
        if: "k" ≤ nodeKey "succ" then ("pred", "succ")
        else "find" "succ" "k" "lvl".
  
  Definition findLock : val := 
    rec: "find" "pred" "k" "lvl" :=
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := !(nodeLocks "pred" +ₗ "lvl") in
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

  Definition get : val :=
    λ: "p" "k", 
      let: "pair" := findAll !"p" "k" #MAX_HEIGHT #0 in
      let: "succ" := Snd "pair" in
        if: "k" ≠ nodeKey "succ" then NONEV
        else let: "val" := !(nodeVal "succ") in SOME (Fst "val").

  Definition link : val := 
    λ: "pred" "lvl" "n",
      let: "new" := !"n" in
        nodeNext "new" +ₗ "lvl" <- !(nodeNext "pred" +ₗ "lvl") ;;
        nodeLocks "new" +ₗ "lvl" <- newlock #();;
        nodeNext "pred" +ₗ "lvl" <- "n".

  Definition insert : val := 
    λ: "pred" "lvl" "n",
      let: "k" := nodeKey !"n" in
      let: "pair" := findLock "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := !(nodeLocks "pred" +ₗ "lvl") in
        link "pred" "lvl" "n";;
        release "lock".

  Definition createAndLink : val := 
    λ: "pred" "k" "v" "t" "h",
      let: "next" := AllocN ("h" + #1) #() in
      let: "locks" := AllocN ("h" + #1) #() in
      let: "val" := ref ("v", "t", #dummy_null) in
      let: "n" := ref ("k", "val", "next", NONEV, #(), "locks") in
        link "pred" #0 "n";;
        "n".

  Definition update : val := 
    λ: "node" "v" "t",
      let: "val" := !(nodeVal "node") in
        if: "t" < valTs "val" then #()
        else nodeVal "node" <- ("v", "t", ref "val").

  Definition tryInsert : val := 
    λ: "pred" "k" "v" "t" "h",
      let: "pair" := findLock "pred" "k" #0 in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
      let: "lock" := !(nodeLocks "pred") in
        if: "k" = nodeKey "succ"
        then update "succ" "v" "t";;
             release "lock";;
             NONEV
        else let: "n" := createAndLink "pred" "k" "v" "t" "h" in
               release "lock";;
               SOME "n".
      
  Definition insertAll : val := 
    rec: "insert" "curr" "k" "v" "t" "h" "lvl" := 
      if: "lvl" = #0 then tryInsert "curr" "k" "v" "t" "h"
      else let: "pair" := find "curr" "k" ("lvl" - #1) in
           let: "pred" := Fst "pair" in
           let: "opt" := "insert" "pred" "k" "v" "t" "h" ("lvl" - #1) in
             match: "opt" with
               NONE => NONEV
             | SOME "n" => insert "curr" "lvl" "n";;
                           SOME "n"
             end.

  Definition put : val := 
    λ: "p" "k" "v" "t" "h",
      let: "pair" := findAll !"p" "k" #MAX_HEIGHT "h" in
      let: "pred" := Fst "pair" in
      let: "_" := insertAll "pred" "k" "v" "t" "h" "h" in #().

End SkipList.
