From AtomicInvariant.atomic Require Import lock.
From iris.heap_lang Require Import notation.


Section node_rep.
  Definition node_rep : Type := Z * loc * loc * loc.
  Definition dummy_null : loc := {|loc_car := 0|}.

  Definition node_key (n: node_rep) : Z := n.1.1.1.
  Definition node_val (n: node_rep) : loc := n.1.1.2.
  Definition node_next (n: node_rep) : loc := n.1.2.
  Definition node_lock (n: node_rep) : loc := n.2.

  Definition nodeKey : val := λ: "l", Fst (Fst (Fst "l")).
  Definition nodeVal : val := λ: "l", Snd (Fst (Fst "l")).
  Definition nodeNext : val := λ: "l", Snd (Fst "l").
  Definition nodeLock : val := λ: "l", Snd "l".

  Definition rep_to_node (n: node_rep) : val :=
    (#(node_key n), #(node_val n), #(node_next n), #(node_lock n)).
  Lemma fold_rep_to_node (n: node_rep) :
    ((#(node_key n), #(node_val n), #(node_next n), #(node_lock n)))%V = rep_to_node n.
  Proof. done. Qed.
  Lemma rep_to_node_inj rep rep':
    rep_to_node rep = rep_to_node rep' → rep = rep'.
  Proof.
    destruct rep as (((?&?)&?)&?); destruct rep' as (((?&?)&?)&?).
    rewrite /rep_to_node/node_key/node_val/node_next/node_lock/=; congruence.
  Qed.
End node_rep.

Section val_rep.
  Local Open Scope Z.
  Definition val_rep : Type := Z * Z * loc.
  Definition dummy_val : val_rep := (0, 0, dummy_null).

  Definition val_v (v: val_rep) : Z := v.1.1.
  Definition val_t (v: val_rep) : Z := v.1.2.
  Definition val_vt (v: val_rep) : Z * Z := v.1.
  Definition val_p (v: val_rep) : loc := v.2.

  Definition valV : val := λ: "l", Fst (Fst "l").
  Definition valT : val := λ: "l", Snd (Fst "l").
  Definition valVT : val := λ: "l", Fst "l".
  Definition valP : val := λ: "l", Snd "l".

  Definition rep_to_val (v: val_rep) : val :=
    (#(val_v v), #(val_t v), #(val_p v)).
  Lemma fold_rep_to_val (v: val_rep) :
    ((#(val_v v), #(val_t v), #(val_p v)))%V =
    rep_to_val v.
  Proof. done. Qed.
  Lemma rep_to_val_inj rep rep' :
    rep_to_val rep = rep_to_val rep' →
    rep = rep'.
  Proof.
    destruct rep as ((?&?)&?); destruct rep' as ((?&?)&?).
    rewrite /rep_to_val/val_v/val_t/val_p/=; congruence.
  Qed.
End val_rep.

Module Type SKIP_LIST_PARAMS.
  Local Open Scope Z.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter MAX_HEIGHT : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
  Parameter (HMAX_HEIGHT: 0 ≤ MAX_HEIGHT).
End SKIP_LIST_PARAMS.

Module AtomicInvariant (Params: SKIP_LIST_PARAMS).
  Import Params.

  Definition tail : node_rep := (INT_MAX, dummy_null, dummy_null, dummy_null).

  Definition newMap : val :=
    λ: "_",
      let: "nexts" := AllocN #(MAX_HEIGHT + 1) (ref (rep_to_node tail)) in
      let: "locks" := AllocN #(MAX_HEIGHT + 1) #false in
        ref (#INT_MIN, #dummy_null, "nexts", "locks").

  Definition find : val :=
    rec: "find" "pred" "k" "lvl" :=
      let: "succ" := ! !(nodeNext "pred" +ₗ "lvl") in
        if: "k" ≤ nodeKey "succ" then ("pred", "succ")
        else "find" "succ" "k" "lvl".

  Definition findLock : val :=
    rec: "find" "pred" "k" "lvl" :=
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" +ₗ "lvl" in
        acquire "lock";;
        let: "succ" := ! !(nodeNext "pred" +ₗ "lvl") in
          if: "k" ≤ nodeKey "succ" then ("pred", "succ")
          else release "lock";;
               "find" "succ" "k" "lvl".

  Definition findAll : val :=
    rec: "find" "pred" "k" "lvl" :=
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
        if: "k" = nodeKey "succ"
        then let: "val" := !(nodeVal "succ") in SOME (valVT "val")
        else if: "lvl" = #0 then NONEV
             else "find" "pred" "k" ("lvl" - #1).

  Definition get : val :=
    λ: "p" "k", findAll !"p" "k" #MAX_HEIGHT.

  Definition createAndLink : val :=
    λ: "pred" "k" "v" "t" "h",
      let: "nexts" := AllocN ("h" + #1) #() in
      let: "locks" := AllocN ("h" + #1) #false in
      let: "val" := ref ("v", "t", #dummy_null) in
      let: "n" := ref ("k", "val", "nexts", "locks") in
        nodeNext !"n" <- !(nodeNext "pred");;
        nodeNext "pred" <- "n";;
        "n".
  
  Definition update : val :=
    λ: "node" "v" "t",
      let: "val" := !(nodeVal "node") in
        if: "t" < valT "val" then #()
        else nodeVal "node" <- ("v", "t", ref "val").

  Definition tryInsert : val :=
    λ: "pred" "k" "v" "t" "h",
      let: "pair" := findLock "pred" "k" #0 in
      let: "pred" := Fst "pair" in
      let: "succ" := Snd "pair" in
      let: "lock" := nodeLock "pred" in
        if: "k" = nodeKey "succ"
        (* Update existing node *)
        then update "succ" "v" "t";;
             release "lock";;
             NONEV
        (* Allocate and insert new node *)
        else let: "n" := createAndLink "pred" "k" "v" "t" "h" in
               release "lock";;
               SOME "n".

  Definition insert : val :=
    λ: "pred" "lvl" "n",
      let: "k" := nodeKey !"n" in
      let: "pair" := findLock "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
      let: "lock" := nodeLock "pred" +ₗ "lvl" in
        nodeNext !"n" +ₗ "lvl" <- !(nodeNext "pred" +ₗ "lvl");;
        nodeNext "pred" +ₗ "lvl" <- "n";;
        release "lock".

  Definition findLevel : val :=
    rec: "find" "pred" "k" "lvl" "h" :=
      let: "pair" := find "pred" "k" "lvl" in
      let: "pred" := Fst "pair" in
        if: "lvl" = "h" then "pred"
        else "find" "pred" "k" ("lvl" - #1) "h".

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

  Definition putH : val :=
    λ: "p" "k" "v" "t" "h",
      let: "pred" := findLevel !"p" "k" #MAX_HEIGHT "h" in
      let: "_" := insertAll "pred" "k" "v" "t" "h" "h" in #().

  (* Base HeapLang does not support randomness... *)
  Definition randomLevel : val :=
    λ: "_", #0.

  Definition put : val :=
    λ: "p" "k" "v" "t",
      let: "h" := randomLevel #() in
        putH "p" "k" "v" "t" "h".

End AtomicInvariant.
