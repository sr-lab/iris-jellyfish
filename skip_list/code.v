From SkipList.lib Require Import lock.
From SkipList.skip_list Require Import node_rep.


Local Open Scope Z.
Module Type SKIP_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter MAX_HEIGHT : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End SKIP_LIST_PARAMS.

Definition nodeKey : val := λ: "l", Fst (Fst (Fst "l")).
Definition nodeNext : val := λ: "l", Snd (Fst (Fst "l")).
Definition nodeDown : val := λ: "l", Snd (Fst "l").
Definition nodeLock : val := λ: "l", Snd "l".

Module SkipList (Params: SKIP_LIST_PARAMS).
  Import Params.

  (* 
   * (node_down tail) is never called, so there's no problem 
   * in having None for all levels here.
   * The same can be said for (node_lock tail) and the dummy_lock.
   *)
  Definition dummy_lock : val := #{|loc_car := 0|}.
  Definition tail : node_rep := (INT_MAX, None, None, dummy_lock).

  (* Lazy list creation *)
  Definition newLoop : val := 
    rec: "loop" "head" "l" :=
      let: "h" := ref "head" in
      if: "l" = #MAX_HEIGHT
      then "h"
      else
        let: "t" := ref (rep_to_node tail) in
        let: "head" := (#INT_MIN, SOME "t", SOME "h", newlock #()) in
        "loop" "head" ("l" + #1).
  
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      let: "head" := (#INT_MIN, SOME "t", NONEV, newlock #()) in
      let: "h" := newLoop "head" #0 in
      "h".

  (* Find functions *)
  Definition find : val := 
    rec: "find" "pred" "k" :=
      let: "ocurr" := (nodeNext "pred") in
      match: "ocurr" with
          NONE => NONEV
        | SOME "np" => 
          let: "curr" := !"np" in
          let: "ck" := (nodeKey "curr") in
          if: "k" ≤ "ck"
          then SOME ("pred", "curr")
          else "find" "curr" "k"
      end.
  
  Definition findLock : val := 
    rec: "find" "head" "k" :=
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => NONEV
        | SOME "pair" =>
          let: "pred" := Fst "pair" in
          let: "curr" := Snd "pair" in
          acquire (nodeLock "pred");;
          let: "onext" := (nodeNext "pred") in
          match: "onext" with
              NONE => NONEV
            | SOME "np" =>
              let: "next" := !"np" in
              let: "nk" := (nodeKey "next") in
              let: "ck" := (nodeKey "curr") in
              if: "nk" = "ck" 
              then SOME ("pred", "curr")
              else
                release (nodeLock "pred");;
                "find" "head" "k"
          end
      end.

  (* Lazy list lookup *)
  Definition findPred : val := 
    rec: "find" "head" "k" := 
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => NONEV
        | SOME "pair" =>
          let: "pred" := Fst "pair" in
          let: "curr" := Snd "pair" in
          match: nodeDown "pred" with
              NONE => SOME ("pred", "curr")
            | SOME "np" => 
              let: "pred" := !"np" in
              "find" "pred" "k"
          end
      end.

  Definition contains : val := 
    λ: "head" "k", 
      let: "opair" := findPred "head" "k" in
      match: "opair" with
          NONE => #false
        | SOME "pair" => 
          let: "curr" := Snd "pair" in
          let: "ck" := nodeKey "curr" in
          "k" = "ck"
      end.

  (* Top Level *)
  Definition topLevelLoop : val := 
    rec: "loop" "head" "k" "h" "l" :=
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => NONEV
        | SOME "pair" =>
          let: "pred" := Fst "pair" in
          if: "h" = "l"
          then "pred"
          else
            "loop" "pred" "k" "h" "l"-#1
      end.
  
  Definition topLevel : val :=
    λ: "head" "k" "h", topLevelLoop "head" "k" "h" #MAX_HEIGHT.

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
        match: nodeNext "pred" with
            NONE => release (nodeLock "pred")
          | SOME "np" =>
            let: "succ" := !"np" in
            let: "next" := ref "succ" in
            let: "node" := ("k", SOME "next", NONEV, newlock #()) in
            "np" <- "node";;
            release (nodeLock "pred");;
            SOME "node"
        end.

  Definition insert : val := 
    λ: "head" "k" "down",
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      match: nodeNext "pred" with
          NONE => release (nodeLock "pred")
        | SOME "np" =>
          let: "succ" := !"np" in
          let: "next" := ref "succ" in
          let: "node" := ("k", SOME "next", SOME "down", newlock #()) in
          "np" <- "node";;
          release (nodeLock "pred");;
          SOME "node"
      end.

  (* Skip list insertion *)
  Definition addAll : val := 
    rec: "add" "head" "k" := 
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => NONEV
        | SOME "pair" =>
          let: "pred" := Fst "pair" in
          let: "curr" := Snd "pair" in
          match: nodeDown "pred" with
              NONE => tryInsert "pred" "k"
            | SOME "np" => 
              let: "pred" := !"np" in
              let: "onode" := "add" "pred" "k" in
              match: "onode" with 
                  NONE => NONEV
                | SOME "node" => insert "pred" "k" "node"
              end
          end
      end.

  Definition add : val := 
    λ: "head" "k" "h",
      let: "opred" := topLevel "head" "k" "h" in
      match: "opred" with
          NONE => #false
        | SOME "pred" => 
          let: "onode" := addAll "pred" "k" in
          match: "onode" with
              NONE => #false
            | SOME "node" => #true
          end
      end.

End SkipList.
