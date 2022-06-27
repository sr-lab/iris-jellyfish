From SkipList.lib Require Import lock node_rep.


Local Open Scope Z.

Module Type LAZY_LIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End LAZY_LIST_PARAMS.

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
            "find" "pred" "k"
        end
      end.
  
  Definition dummy_lock : val := #{|loc_car := 0|}.
  Definition tail : node_rep := (INT_MAX, None, None, dummy_lock).  

  (* Lazy list creation *)
  Definition new : val := 
    λ: "_", 
      let: "t" := ref (rep_to_node tail) in
      ref (#INT_MIN, SOME "t", NONEV, newlock #()).

  (* Lazy list lookup *)
  Definition contains : val := 
    λ: "head" "k",
      let: "opair" := find !"head" "k" in
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
      let: "opair" := findLock !"head" "k" in
      match: "opair" with
        NONE => #false
      | SOME "pair" =>
        let: "pred" := Fst "pair" in
        let: "curr" := Snd "pair" in
        let: "ck" := (nodeKey "curr") in
        if: "k" = "ck"
        then
          release (nodeLock "pred");;
          #false
        else
          match: nodeNext "pred" with
            NONE =>
            release (nodeLock "pred");;
            #false
          | SOME "np" =>
            let: "succ" := !"np" in
            let: "next" := ref "succ" in
            let: "node" := ("k", SOME "next", NONEV, newlock #()) in
            "np" <- "node";;
            release (nodeLock "pred");;
            #true
          end
      end.

End LazyList.
