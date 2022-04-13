From SkipList.lib Require Import lock.
From SkipList.lib Require Export misc.


Local Open Scope Z.
Module Type LAZY_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

Definition nodeKey : val := λ: "l", Fst (Fst (Fst "l")).
Definition nodeNext : val := λ: "l", Snd (Fst (Fst "l")).
Definition nodeMark : val := λ: "l", Snd (Fst "l").
Definition nodeLock : val := λ: "l", Snd "l".

Module LazyList (Params: LAZY_LIST_PARAMS).
  Import Params.

  (* Auxiliary function *)
  Definition validate : val := 
    λ: "pred" "curr", 
      (* let: "pred_mark" := (nodeMark "pred") in
      let: "curr_mark" := (nodeMark "curr") in *)
      let: "onext" := (nodeNext "pred") in
      match: "onext" with
          NONE => #false
        | SOME "np" =>
          let: "next" := !"np" in
          "curr" = "next" 
            (* && ("pred_mark" = #false) && ("curr_mark" = #false) *)
      end.
  
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
          let: "curr" := Snd "curr" in
          acquire (nodeLock "pred");;
          if: validate "pred" "curr"
          then
            ("pred", "curr")
          else
            release (nodeLock "pred");;
            "find" "head" "k"
      end.
  
  
  Definition dummy_lock : val := #{|loc_car := 0|}.
  Definition tail : node_rep := (INT_MAX, None, false, dummy_lock).  

  (* Lazy list creation *)
  Definition new : val := 
    λ: "_", (#INT_MIN, SOME (ref (rep_to_node tail)), #false, dummy_lock).

  (* Lazy list lookup *)
  Definition contains : val := 
    λ: "head" "k",
      let: "opair" := find "head" "k" in
      match: "opair" with
          NONE => #false
        | SOME "pair" =>
          let: "curr" := Snd "pair" in
          let: "ck" := (nodeKey "curr") in
          (* let: "cm" := (nodeMark "curr") in *)
          ("k" = "ck") 
            (* && ("cm" = #false) FIXME *)
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
        release (nodeLock "pred");;
        #false
      else
        let: "osucc" := nodeNext "pred" in
        let: "node" := ("k", "osucc", #false, newlock #()) in
        match: "osucc" with
            NONE =>
            release (nodeLock "pred");;
            #false
          | SOME "np" =>
            "np" <- "node";;
            release (nodeLock "pred");;
            #true
        end.
  
  (* Lazy list removal *)
  Definition remove : val := 
    rec: "find" "pred" "k" :=
      let: "curr" := !(nodeNext "pred") in
      match: "curr" with
          NONE => #false (* tail node *)
        | SOME "node" =>
          let: "ck" := (nodeKey "node") in
          if: "k" ≤ "ck"
          then
            acquire (nodeLock "pred");;
            acquire (nodeLock "node");;
            if: (validate "pred" "node")
            then 
              if: ("ck" = "k")
              then
                (nodeMark "node") <- #true;;
                (nodeNext "pred") <- !(nodeNext "node");;
                release (nodeLock "node");;
                release (nodeLock "pred");;
                #true
              else
                release (nodeLock "node");;
                release (nodeLock "pred");;
                #false
            else
              release (nodeLock "node");;
              release (nodeLock "pred");;
              "find" "pred" "k" (* Retry *)
          else
            "find" "node" "k"
      end.

End LazyList.
