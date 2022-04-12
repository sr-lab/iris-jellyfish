From SkipList.lib Require Import misc lock.


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
      let: "next" := !(nodeNext "pred") in
      let: "pred_mark" := (nodeMark "pred") in
      let: "curr_mark" := (nodeMark "curr") in
      ("pred_mark" = #false) && ("curr_mark" = #false) && ("next" = SOME "curr").
  
  Definition find : val := 
    rec: "find" "pred" "k" :=
      let: "curr" := (nodeNext "pred") in
      match: "curr" with
          NONE => NONEV
        | SOME "np" => 
          let: "node" := !"np" in
          let: "ck" := (nodeKey "node") in
          if: "k" ≤ "ck"
          then SOME "node"
          else "find" "node" "k"
      end.

  (* FIXME remove this and replace with newlock #() *)
  Definition dummy_lock : val := #1.

  Definition tail : node_rep := (INT_MAX, None, false, dummy_lock).  

  (* Lazy list creation *)
  Definition new : val := 
    λ: "_", (#INT_MIN, SOME (ref (rep_to_node tail)), #false, dummy_lock).

  (* Lazy list lookup *)
  Definition contains : val := 
    λ: "head" "k",
      let: "ocurr" := find "head" "k" in
      match: "ocurr" with
          NONE => #false
        | SOME "curr" =>
          let: "ck" := (nodeKey "curr") in
          (* let: "cm" := (nodeMark "curr") in *)
          ("k" = "ck") (* && ("cm" = #false) FIXME *)
      end.
  
  (* Lazy list insertion *)
  Definition add : val := 
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
                release (nodeLock "node");;
                release (nodeLock "pred");;
                #false
              else
                let: "node" := ("k", ("curr", (#false, newlock #()))) in
                (nodeNext "pred") <- "node";;
                release (nodeLock "node");;
                release (nodeLock "pred");;
                #true
            else
              release (nodeLock "node");;
              release (nodeLock "pred");;
              "find" "pred" "k" (* Retry *)
          else
            "find" "node" "k"
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
