From SkipList.lib Require Import lock.
From SkipList.lib Require Export misc.


Local Open Scope Z.
Module Type LAZY_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

Definition nodeKey : val := λ: "l", Fst (Fst "l").
Definition nodeNext : val := λ: "l", Snd  (Fst "l").
Definition nodeLock : val := λ: "l", Snd "l".

Module LazyList (Params: LAZY_LIST_PARAMS).
  Import Params.

  (* Auxiliary functions *)
  
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
          NONE => #false
        | SOME "pair" =>
          let: "pred" := Fst "pair" in
          let: "curr" := Snd "pair" in
          acquire (nodeLock "pred");;
          let: "onext" := (nodeNext "pred") in
          match: "onext" with
              NONE => #false
            | SOME "np" =>
              let: "next" := !"np" in
              let: "nk" := (nodeKey "next") in
              let: "ck" := (nodeKey "curr") in
              if: "nk" = "ck" 
              then
                ("pred", "curr")
              else
                release (nodeLock "pred");;
                "find" "head" "k"
          end
      end.
  
  Definition dummy_lock : val := #{|loc_car := 0|}.
  Definition tail : node_rep := (INT_MAX, None, dummy_lock).  

  (* Lazy list creation *)
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      (#INT_MIN, SOME "t", newlock #()).

  (* Lazy list lookup *)
  Definition contains : val := 
    λ: "head" "k",
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => #false
        | SOME "pair" =>
          let: "curr" := Snd "pair" in
          let: "ck" := (nodeKey "curr") in
          ("k" = "ck") 
      end.
  
  (* Lazy list insertion *)
  Definition add : val := 
    λ: "head" "k",
      let: "pair" := findLock "head" "k" in
      let: "pred" := Fst "pair" in
      let: "curr" := Snd "pair" in
      let: "ck" := (nodeKey "curr") in
      if: "k" = "ck"
      then
        release (nodeLock "pred")
      else
        match: nodeNext "pred" with
            NONE =>
            release (nodeLock "pred")
          | SOME "np" =>
            let: "succ" := !"np" in
            let: "next" := ref "succ" in
            let: "node" := ("k", SOME "next", newlock #()) in
            "np" <- "node";;
            release (nodeLock "pred")
        end.

End LazyList.
